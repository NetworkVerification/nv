#!/usr/bin/env python3
"""
gen_part_nv.py [nvfile]
A module for generating spX-part.nv fileoutput from spX.nv files.
"""
import itertools
import math
import os
import pathlib
import re
import argparse
import subprocess
from typing import Literal, Optional
from utils import If, NetType, NodeGroup, FattreeCut, AttrType, Bgp, Rib

# used for constructing the graph
import igraph


def preamble(file_info):
    """
    Return the list of preamble strings.
    """
    vim_modeline = "(* vim: set syntax=ocaml: *)"
    generated_by = "(* Automatically generated by gen_part_nv.py *)"
    return [vim_modeline, file_info, generated_by]


class NvFile:
    """
    Representation of an NV file's internal information.

    We load the network in from the given path as self.mono.
    """

    def __init__(
        self,
        path: str,
        net_type: NetType,
        dest: int,
        simulate: bool = False,
        verbose: bool = False,
        groups: bool = True,
    ):
        """
        Initialize an NvFile.

        If dest is given, use it to set the destination node.
        If verbose is true, print the constructed graph.
        If groups is true, use the comment in the file to assign nodes to fattree groups.
        """
        self.path = path
        self.net = net_type
        self.dest = dest
        self.verbose = verbose
        with open(path) as f:
            self.mono = f.read()
        self.attr = AttrType.parse_from_file(self.mono)
        self.graph = construct_graph(self.mono, groups)
        if self.verbose:
            print(self.print_graph())
        if simulate:
            self.sols = run_nv_simulate(self.path)
            if self.net is NetType.MAINTENANCE:
                pat = re.compile(r"aslen=\s*\d*u32")
                aslens = get_maintenance_paths(self.graph, self.dest, 1)
                # update the solution's aslen using the cases provided by the tree exploration
                for (node, sol) in self.sols.items():
                    self.sols[node] = pat.sub(f"aslen={aslens[node]}", sol)
        else:
            self.infer_sol()

    def infer_sol(self):
        """Infer the solutions to the network."""
        match self.net:
            case NetType.SP | NetType.FATPOL | NetType.RAND | NetType.OTHER:
                self.sols = infer_single_destination_routes(
                    self.graph, self.dest, self.attr, NetType is NetType.FATPOL
                )
                if self.attr == AttrType.INT_OPTION or self.attr == AttrType.BGP:
                    # tag Some/None for solutions
                    self.sols = {
                        v: (f"Some {x}" if x else "None") for v, x in self.sols.items()
                    }
            case NetType.AP if self.attr is AttrType.RIB:
                # TODO: add APPOL support
                # need to determine each node's pod and prefix to figure out when it is the destination
                self.sols = infer_all_tor_destination_routes(
                    self.graph, self.net is NetType.APPOL
                )
            case NetType.MAINTENANCE:
                aslens = get_maintenance_paths(self.graph, self.dest, 1)
                self.sols = {}
                for (node, sol) in infer_single_destination_routes(
                    self.graph, self.dest, self.attr, False
                ).items():
                    # update the aslen from the maintenance paths
                    if isinstance(sol, Rib) and sol.bgp:
                        sol.bgp.aslen = aslens[node]
                        self.sols[node] = Rib(sol.bgp, sol.static).select()
                    elif isinstance(sol, int):
                        self.sols[node] = f"Some {aslens[node]}"
                    elif isinstance(sol, Bgp):
                        sol.aslen = aslens[node]
                        self.sols[node] = f"Some {sol}"
                    elif sol is None:
                        self.sols[node] = "None"
                    elif isinstance(sol, Rib) and not sol.bgp:
                        raise TypeError(
                            "can't assign maintenance path to a node without BGP attribute set"
                        )
                    else:
                        raise TypeError(
                            f"unexpected solution type during infer_sol: {type(sol)}"
                        )
            case _:
                print(
                    f"Can't infer solutions of a {self.net} network: try running {os.path.basename(__file__)} with the simulate flag on."
                )
                self.sols = None

    def fat_cut(self, cut_type: FattreeCut):
        """
        Given the cut, generate a new NV file with partition and interface functions.
        """
        match cut_type:
            case FattreeCut.VERTICAL:
                nodes = nodes_cut_vertically(self.graph, self.dest)
            case FattreeCut.HORIZONTAL:
                nodes = nodes_cut_horizontally(self.graph, self.dest)
            case FattreeCut.PODS:
                nodes = nodes_cut_pods(self.graph, self.dest)
            case FattreeCut.SPINES:
                nodes = nodes_cut_spines(self.graph, self.dest)
            case FattreeCut.FULL:
                nodes = nodes_cut_fully_connected(self.graph, self.dest)
        match self.net:
            case NetType.FATPOL if cut_type is FattreeCut.VERTICAL:
                # special case for handling vertical cuts
                edges = get_vertical_cross_edges(self.graph, nodes, self.dest)
            case NetType.FATPOL | NetType.SP | NetType.AP | NetType.MAINTENANCE:
                edges = get_cross_edges(self.graph, nodes, ranked=False)
            case _:
                raise TypeError(f"Invalid network type {self.net} for fat_cut")
        return nodes, edges

    def rand_cut(self):
        nodes = nodes_cut_fully_disconnected(self.graph)
        edges = get_cross_edges(self.graph, nodes, ranked=False)
        return nodes, edges

    def hmetis_cut(self, hgr_part: str):
        """
        Produce a cut based on a hypergraph partitioning produced by hMETIS.
        :field hgr_part: a path to an .hgr file.
        """
        with open(hgr_part) as partf:
            # produce a mapping from nodes (lines) to partitions
            lines = partf.readlines()
        # increment the index by 1 and wrap around to change the last node into node 0
        mapping = {(i + 1) % len(lines): int(p) for (i, p) in enumerate(lines)}
        nodes: list[list[int]] = [[]]
        # sort the mapped nodes into their partitions
        for (i, p) in mapping.items():
            for _ in range(len(nodes), p + 1):
                nodes.append([])
            nodes[p].append(i)
        if self.sols:
            edges = get_cross_edges(self.graph, nodes, ranked=False)
        else:
            raise Exception("Can't rank cross edges for hMETIS cut networks.")
        return nodes, edges

    def generate_parted(self, nodes, edges):
        partition = write_partition_str(nodes)
        interface = write_interface_str(edges, self.sols)
        # perform the decomposed transfer on the input side
        repl = (
            r"solution { init = init; trans = trans; merge = merge;"
            r" interface = interface; rtrans = trans }"
        )
        text = re.sub(r"solution {.*}", repl, self.mono)
        # put 'em all together
        return "\n".join([text, partition, interface])

    def print_graph(self):
        return str(self.graph)

    def to_graphml(self, outfile):
        self.graph.write_graphmlz(outfile)


def construct_graph(text: str, groups=True) -> igraph.Graph:
    """
    Construct a digraph from the given edge and node information.
    Vertices have three attributes:
    - g: the vertex group
    - p: the vertex pod
    - addr: the associated IPv4 address
    The pod and addr are only included if groups is True.
    """
    g = igraph.Graph(directed=True)
    if groups:
        nodes = find_nodes(text)
        npods = int(math.sqrt(len(nodes) * 0.8))
        ncores = (npods // 2) ** 2
    else:
        nodes = find_nodes_nogroups(text)
        npods = 0
        ncores = 0
    for (v, grp, old_num) in nodes:
        if old_num is None:
            g.add_vertex(g=grp, p=None)
        else:
            bf_node = int(old_num)
            if bf_node < ncores:
                pod = npods
            else:
                pod = (int(old_num) - ncores) // npods
            # compute the ip address of this node's /24 prefix
            addr = 70 * 256**3 + bf_node * 256
            g.add_vertex(g=grp, p=pod, addr=addr)
    edges = find_edges(text)
    g.add_edges(edges)
    # add stable node numbering
    for v in g.vs:
        v["id"] = v.index
    return g


def get_maintenance_paths(graph: igraph.Graph, dest: int, num_down: int):
    """
    Get all the paths from nodes to the destination, when up to num_down nodes
    may be down for maintenance.
    """
    # paths is a dict of dicts: the first key is the node,
    # and the internal dict maps path length keys to a list of which nodes are down
    # we can then use the lists of down nodes to derive an interface describing
    # the number of hops
    paths = {v: {} for v in range(graph.vcount())}
    for k in range(1, num_down + 1):
        combinations = itertools.combinations(graph.vs.select(id_ne=dest), k)
        # iterate over each combination of down nodes
        for nodes in combinations:
            g = graph.copy()
            g.delete_vertices(nodes)
            d = g.vs.find(id=dest)
            ps = g.get_shortest_paths(d)
            # map the terminal element to this path
            # subtract one from the length, since we want the number of hops
            p = [(g.vs[path[-1]]["id"], len(path) - 1) for path in ps]
            for (v, plen) in p:
                # add cases for each possible path length
                cases = paths[v].setdefault(plen, [])
                cases.append([v["id"] for v in nodes])
    return {k: write_maintenance_aslen(v) for k, v in paths.items()}


def write_maintenance_aslen(lengths):
    # NOTE: assumes at most 1 node down and cases which are singleton lists
    if len(lengths.keys()) == 1:
        aslen = str(list(lengths.keys())[0])
    elif len(lengths.keys()) == 2:
        items = list(lengths.items())
        items.sort(key=lambda x: len(x[1]))
        aslen = str(
            If(f"down = Some({items[0][1][0][0]})", f"{items[0][0]}", f"{items[1][0]}")
        )
    else:
        aslen = "match down with "
        for (l, cases) in lengths:
            aslen += " ".join([f"| Some {c[0]}" for c in cases]) + f" -> {l}"
    return aslen


def infer_node_comms(graph: igraph.Graph, path: list[int]) -> set[int]:
    """
    Return a set of BGP community tags inferred from the given AS path.
    """
    return set(graph.vs[i]["g"].community(graph.vs[i]["p"], False) for i in path)


def infer_single_destination_routes(
    graph: igraph.Graph, dest: int, attr_type: AttrType, policy: bool
) -> dict[int, Bgp | Rib | int | None]:
    """
    Infer the shortest path to the destination for each node.
    Return a RIB if the attribute type is RIB, or an integer if it's an INT_OPTION.
    If policy is True, then when the attribute type is BGP or RIB, community tags
    will be inferred, as in the fatXPol benchmarks.
    """

    def create_route(i: int, path: list[int]) -> tuple[int, Bgp | Rib | int | None]:
        """i is a vertex id, path is a list of vertex ids"""
        node = graph.vs[i]["id"]
        if len(path) == 0:
            return node, None
        hops = len(path) - 1
        match attr_type:
            case AttrType.INT_OPTION:
                return node, hops
            case AttrType.RIB:
                # generate a rib from the given BGP value and with possibly a static route
                # call select() to assign the selected route
                if policy:
                    bgp = Bgp(aslen=hops, comms=set(infer_node_comms(graph, path)))
                else:
                    bgp = Bgp(aslen=hops)
                return node, Rib(bgp, static=1 if node == dest else None).select()
            case AttrType.BGP:
                if policy:
                    bgp = Bgp(aslen=hops, comms=set(infer_node_comms(graph, path)))
                else:
                    bgp = Bgp(aslen=hops)
                return node, bgp

    d = graph.vs.find(id=dest)
    # mode="out" gives us the path to the destination from that node
    ps = graph.get_shortest_paths(d, mode="out")
    # ps is a list of lists of vertex ids
    return dict(create_route(i, path) for i, path in enumerate(ps))


def infer_all_tor_destination_routes(
    graph: igraph.Graph, policy: bool
) -> dict[int, Rib]:
    """
    Infer the solutions for each node when the destination is symbolic.
    If policy is True, then community tags
    will be inferred, as in the fatXPol benchmarks.
    """
    # TODO: the specific community tags will depend on the destination's pod;
    # every destination has its own particular sequence of tags unfortunately
    sols = {}
    for node in graph.vs:
        if node["g"] == NodeGroup.CORE:
            sols[node["id"]] = Rib(bgp=Bgp(aslen=2)).select()
        elif node["g"] == NodeGroup.AGGREGATION:
            sols[node["id"]] = Rib(
                bgp=Bgp(aslen=str(If(f"pod = {node['p']}", 1, 3)))
            ).select()
        elif node["g"] == NodeGroup.EDGE:
            # don't call select() here since we set it ourselves according to the symbolic
            aslen = str(
                If(
                    # case where this node is the destination
                    f"pod = {node['p']} && d = ({node['addr']}, 24u6)",
                    0,
                    # case where this node is in the destination's pod or not
                    If(f"pod = {node['p']}", 2, 4),
                )
            )
            sols[node["id"]] = Rib(
                bgp=Bgp(
                    aslen=aslen,
                ),
                static=str(If(f"d = ({node['addr']}, 24u6)", "Some 1u8", "None")),
                selected=str(If(f"d = ({node['addr']}, 24u6)", "Some 1u2", "Some 3u2")),
            )
        else:
            raise Exception(f"Invalid node group {node['g']}")
    return sols


def node_to_int(node: str) -> int:
    return int(node.rstrip("n"))


def find_edges(text: str) -> list[tuple[int, int]]:
    """Return the edges."""

    def to_int(match, flip=False):
        """
        Return a directed edge associated with the given match.
        If flip is true, return the reverse edge.
        """
        if flip:
            return (node_to_int(match.group(2)), node_to_int(match.group(1)))
        else:
            return (node_to_int(match.group(1)), node_to_int(match.group(2)))

    directed = r"(\d+n?)-(\d+n?);"
    undirected = r"(\d+n?)=(\d+n?);"
    prog = re.compile(directed)
    matches = prog.finditer(text)
    outputs = [to_int(m) for m in matches]
    prog = re.compile(undirected)
    matches = prog.finditer(text)
    outputs += [
        e
        for pairs in [[to_int(m), to_int(m, flip=True)] for m in matches]
        for e in pairs
    ]
    # use an intermediate set to remove duplicates, just in case they occur
    outputs = list(set(outputs))
    outputs.sort()
    return outputs


def find_nodes(text: str) -> list[tuple[int, NodeGroup, Optional[str]]]:
    """Return the nodes, along with an associated NodeGroup and node number, if present."""
    # first group "ng" is the node group
    # second "num" is the old node number
    # third "node" is the NV node number
    pat = r"(?P<ng>\w+)(?:(?:-|_)(?P<num>\d*))?=(?P<node>\d+)(?:,|})"
    prog = re.compile(pat)
    # find all nodes
    matches = prog.finditer(text)
    # we provide the type annotation here as m.group("num") is not able to confirm that
    # it produces a str
    vertices: list[tuple[int, NodeGroup, Optional[str]]] = [
        (node_to_int(m.group("node")), NodeGroup.parse(m.group("ng")), m.group("num"))
        for m in matches
    ]
    vertices.sort()
    return vertices


def find_nodes_nogroups(text: str) -> list[tuple[int, Literal[NodeGroup.NONE], None]]:
    """Return the nodes with no node groups or old node numbers saved."""
    pat = r"let nodes = (\d*)"
    prog = re.compile(pat)
    # find all nodes
    match = prog.search(text)
    if match:
        vertices = [(v, NodeGroup.NONE, None) for v in range(int(match.group(1)))]
        return vertices
    else:
        raise ValueError("nodes not found")


def write_partition_str(partitions) -> str:
    """
    Return the string representation of the partition function.
    """
    output = "let partition node = match node with\n"
    for i, nodes in enumerate(partitions):
        output += "\n".join([f"  | {node}n -> {i}" for node in nodes]) + "\n"
    return output


def write_interface_str(edges, fmt) -> str:
    output = "let interface edge a ="
    output += "\n  match edge with\n"
    for (start, end) in edges:
        output += f"  | {start}~{end} -> a = {fmt[start]}\n"
    return output


def get_part_fname(nvfile, cutname: str, simulate: bool, overwrite: bool):
    """
    Return the name of the partition file for the corresponding nv file,
    and the network type.
    """
    spdir, spname = os.path.split(nvfile)
    root, nvext = os.path.splitext(spname)
    net_type = NetType.from_filename(root)
    # mark simulated solutions with an x for exact
    sim = "-x" if simulate else ""
    prefix = f"{root}-{cutname}{sim}"
    partfile = os.path.join(spdir, prefix + nvext)
    suffix = 1
    # don't overwrite an existing path: instead, create a new file
    while os.path.exists(partfile) and not overwrite:
        partfile = os.path.join(spdir, prefix + str(suffix) + nvext)
        suffix += 1
    return partfile, net_type


def nodes_cut_fully_connected(graph: igraph.Graph, dest: int) -> list[list[int]]:
    """
    Return the nodes divided up fully into separate partitions.
    Order is established by BFS from the destination if it is given.
    Note that nodes not reachable from the destination will NOT be added.
    """
    return [[v["id"]] for v in graph.bfsiter(dest)]


def nodes_cut_fully_disconnected(graph: igraph.Graph) -> list[list[int]]:
    """
    Return the nodes divided up into individual partitions in arbitrary order.
    Does not require the graph to be connected.
    """
    return [[v["id"]] for v in graph.vs]


def nodes_cut_spines(graph: igraph.Graph, dest: int) -> list[list[int]]:
    """
    Return the nodes divided up such that the destination's pod
    is in one partition, the spine nodes are each in another
    and the other pod nodes are each in another.
    """
    podgraph = graph.subgraph(graph.vs.select(g_ne=NodeGroup.CORE))
    pods = podgraph.decompose()
    dest_idx = 0
    for (i, pod) in enumerate(pods):
        if dest in pod.vs["id"]:
            dest_idx = i
    spines = [v["id"] for v in graph.vs.select(g_eq=NodeGroup.CORE)]
    nondest_pods = [list(pod.vs["id"]) for pod in pods]
    dest_pod = nondest_pods.pop(dest_idx)
    dest_pod.sort()
    spines.sort()
    for pod in nondest_pods:
        pod.sort()
    return [dest_pod] + [[s] for s in spines] + nondest_pods


def nodes_cut_pods(graph: igraph.Graph, dest: int) -> list[list[int]]:
    """
    Return the nodes divided up such that the destination's pod
    is in one partition, the spine nodes are in another and the
    other pod nodes are each in another.
    """
    podgraph = graph.subgraph(graph.vs.select(g_ne=NodeGroup.CORE))
    pods = podgraph.decompose()
    dest_idx = 0
    for (i, pod) in enumerate(pods):
        if dest in pod.vs["id"]:
            dest_idx = i
    spines = [v["id"] for v in graph.vs.select(g_eq=NodeGroup.CORE)]
    nondest_pods = [list(pod.vs["id"]) for pod in pods]
    dest_pod = nondest_pods.pop(dest_idx)
    dest_pod.sort()
    spines.sort()
    for pod in nondest_pods:
        pod.sort()
    return [dest_pod, spines] + nondest_pods


def nodes_cut_horizontally(graph: igraph.Graph, dest: int) -> list[list[int]]:
    """
    Return the nodes divided up such that the destination's pod
    is in one partition, the spine nodes are in another and the
    other pod nodes are in a third.
    """
    podgraph = graph.subgraph(graph.vs.select(g_ne=NodeGroup.CORE))
    pods = podgraph.decompose()
    dest_pod = []
    nondest_pods = []
    for pod in pods:
        if dest in pod.vs["id"]:
            dest_pod = [v["id"] for v in pod.vs]
        else:
            nondest_pods += [v["id"] for v in pod.vs]
    spines = [v["id"] for v in graph.vs.select(g_eq=NodeGroup.CORE)]
    dest_pod.sort()
    spines.sort()
    nondest_pods.sort()
    return [dest_pod, spines, nondest_pods]


def nodes_cut_vertically(graph: igraph.Graph, dest: int) -> list[list[int]]:
    """
    Return the nodes divided up such that half of the spine
    nodes and half of the pods are in one partition
    and the others are in another.
    """
    spines = [v for v in graph.vs.select(g_eq=NodeGroup.CORE)]
    half_spines = spines[: (len(spines) // 2)]
    aggs = [v for v in graph.vs.select(g_eq=NodeGroup.AGGREGATION)]
    half_aggs = aggs[: (len(aggs) // 2)]
    # use a set so as not to add twice
    pods = set()
    for v in half_aggs:
        pods.add(v.index)
        for u in v.neighbors():
            if u["g"] is NodeGroup.EDGE:
                pods.add(u.index)
    # return half of the spines along with the pods
    group1 = [x.index for x in half_spines] + list(pods)
    # get all nodes not in group1
    all_nodes = set(x.index for x in graph.vs)
    group2 = [x for x in all_nodes.difference(set(group1))]
    group1.sort()
    group2.sort()
    if dest in group1:
        return [group1, group2]
    else:
        return [group2, group1]


def get_cross_edges(graph: igraph.Graph, partitions: list[list[int]], ranked=False):
    """
    Get the edges in the network which go between partitions.
    If ranked is True, only include edges which go from lower-ranked partitions
    to higher-ranked partitions.
    These edges are used to determine the interface functions.
    Throws a ValueError if partitions does not contain any node in the graph.
    """
    # check that partitions contains every node in the network.
    if set(v.index for v in graph.vs) != set(v for l in partitions for v in l):
        raise ValueError(
            "get_cross_edges: partitions does not contain every node in graph"
        )
    # construct a map of nodes to their partitions
    n_parts = {node: i for (i, part) in enumerate(partitions) for node in part}

    def edge_predicate(e):
        src = n_parts[e.source]
        tgt = n_parts[e.target]
        return (ranked and src < tgt) or (not ranked and src != tgt)

    return [e.tuple for e in graph.es if edge_predicate(e)]


def get_vertical_cross_edges(
    graph: igraph.Graph, partitions: list[list[int]], dest: int, ranked=False
):
    all_cross = get_cross_edges(graph, partitions, ranked)
    updated = []
    for e in all_cross:
        # prune non-destination-pod cross edges
        node = graph.vs[e[0]]
        neighbors = [v["id"] for v in node.neighbors()]
        if node["g"] is NodeGroup.AGGREGATION and dest not in neighbors:
            continue
        else:
            updated.append(e)
    return updated


def run_nv_simulate(path: str):
    """Run nv's simulation tool and capture its output."""
    nvpath = os.path.join(os.getcwd(), "nv")
    if not os.path.exists(nvpath):
        raise Exception(
            "Could not find 'nv' executable in the current working directory"
        )
    args = [nvpath, "-v", "-s"] + [path]
    print(f"Running {' '.join(args)}")
    try:
        proc = subprocess.run(args, text=True, check=True, capture_output=True)
        pat = re.compile(r"Node (\d+)\n-*\n((?:.|\n)+?)\n\n", re.M)
        return {int(m.group(1)): m.group(2) for m in pat.finditer(proc.stdout)}
    except subprocess.CalledProcessError as exn:
        print(exn.stderr)
        return {}
    except subprocess.TimeoutExpired as exn:
        print(exn.stderr)
        return {}


def gen_part_nv(
    nvfile,
    dest,
    cut: FattreeCut | str,
    simulate=False,
    verbose=False,
    groups=True,
    overwrite=False,
):
    """Generate the partition file."""
    # distinguish fattree cuts from hMETIS cuts
    if isinstance(cut, FattreeCut):
        cut_name = cut.short
        file_info = f"(* {cut.desc} version of {os.path.basename(nvfile)} *)"
    else:
        hmetisn = os.path.basename(cut).split(".")[-1]
        cut_name = f"hmetis{hmetisn}"
        file_info = f"(* hMETIS-partitioned version of {os.path.basename(nvfile)} with {hmetisn} partitions *)"
    # determine the output file name
    part, net_type = get_part_fname(nvfile, cut_name, simulate, overwrite)
    if verbose:
        print("Outfile: " + part)
    nv = NvFile(
        nvfile,
        net_type=net_type,
        dest=dest,
        simulate=simulate,
        verbose=verbose,
        groups=groups,
    )
    # perform the cut
    if net_type.is_fattree() and isinstance(cut, FattreeCut):
        nodes, edges = nv.fat_cut(cut)
    elif (net_type is NetType.OTHER or net_type is NetType.RAND) and isinstance(
        cut, str
    ):
        nodes, edges = nv.hmetis_cut(cut)
    elif net_type is NetType.RAND:
        # rand otherwise defaults to a full cut
        print("Ignoring cut argument for rand network...")
        nodes, edges = nv.rand_cut()
    else:
        raise Exception(
            f"Called gen_part_nv with unexpected cut/net combination: {cut}/{net_type}"
        )
    if verbose:
        print(nodes)
        print([e for e in edges])
    # generate the partitioned network's interface
    partitioned = nv.generate_parted(nodes, edges)
    with open(part, "w") as outfile:
        parts = preamble(file_info)
        parts.append(partitioned)
        outfile.write("\n".join(parts))
    print(f"Saved network to {part}")


def print_graph(nvfile, dest):
    """Print the associated graph for the given NV file."""
    _, spname = os.path.split(nvfile)
    root, _ = os.path.splitext(spname)
    net_type = NetType.from_filename(root)
    nv = NvFile(nvfile, net_type, dest=dest, simulate=False)
    print(nv.print_graph())
    # adj = graph.get_adjlist(mode="all")
    # assert all([len(l) % 2 == 0 for l in adj])


def write_graphml(nvfile, dest):
    _, spname = os.path.split(nvfile)
    root, _ = os.path.splitext(spname)
    p = pathlib.Path(nvfile)
    net_type = NetType.from_filename(root)
    nv = NvFile(nvfile, net_type, dest=dest, simulate=False)
    nv.to_graphml(os.path.join(p.with_suffix(".graphml.gz")))


class ParseFileDest(argparse.Action):
    """
    An argparse parser for collecting files paired with their destination.
    """

    def __call__(self, parser, namespace, values, option_string=None):
        setattr(namespace, self.dest, dict())
        for value in values:
            try:
                f, d = value.split(":")
                getattr(namespace, self.dest)[f] = int(d)
            except ValueError:
                break

    @staticmethod
    def format_usage():
        return "file.nv:node"


def parser():
    parser = argparse.ArgumentParser(
        description="Generate partitioned versions of network benchmarks."
    )
    parser.add_argument(
        "files",
        nargs="+",
        action=ParseFileDest,
        help='unpartitioned network files with their unique associated \
        destination nodes, separated by a colon, e.g. "simple.nv:0"',
    )
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument(
        "-c",
        "--cuts",
        nargs="+",
        choices=FattreeCut.as_list(),
        help="types of cut across the network topology",
    )
    group.add_argument(
        "-k",
        "--hmetis",
        nargs="+",
        help="hMETIS-created partitioning file",
    )
    parser.add_argument(
        "-s",
        "--simulate",
        action="store_true",
        help="generate interface by simulating the given benchmark; ignored when --hmetis is present",
    )
    parser.add_argument(
        "-v", "--verbose", action="store_true", help="increase verbosity"
    )
    parser.add_argument(
        "-ng",
        "--nogroups",
        action="store_false",
        help="don't search for nodes being grouped by any category",
    )
    group.add_argument(
        "-p",
        "--print",
        action="store_true",
        help="print topology info instead of generating partition",
    )
    group.add_argument(
        "-g",
        "--graphml",
        action="store_true",
        help="save to a zipped graphml file instead of generating partition",
    )
    parser.add_argument(
        "-o",
        "--overwrite",
        action="store_true",
        help="overwrite existing files",
    )
    return parser


def main():
    args = parser().parse_args()
    for (file, dest) in args.files.items():
        if args.print:
            print_graph(file, dest)
        elif args.graphml:
            write_graphml(file, dest)
        else:
            # either cuts or hmetis will be true, but not both
            cuts = args.hmetis if args.hmetis else map(FattreeCut.from_str, args.cuts)
            for cut in cuts:
                gen_part_nv(
                    file,
                    dest,
                    cut,
                    simulate=args.simulate,
                    verbose=args.verbose,
                    groups=args.nogroups,
                    overwrite=args.overwrite,
                )


if __name__ == "__main__":
    main()
