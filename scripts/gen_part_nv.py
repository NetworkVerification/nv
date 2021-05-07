#!/usr/bin/env python3
"""
gen_part_nv.py [nvfile]
A module for generating spX-part.nv fileoutput from spX.nv files.
"""
import os
import sys
import re
import argparse
import subprocess
from enum import Enum
from typing import Optional

# used for constructing the graph
import igraph

# Fattree partition cut types
CUTS = [
    # vertical cut: 2 parts
    "v",
    "vertical",
    # horizontal cut: 3 parts
    "h",
    "horizontal",
    # horizontal cut with all pods separate
    "p",
    "pods",
    # horizontal cut with all spines and pods separate
    "s",
    "spines",
    # full cut with every node in its own partition
    "f",
    "full",
]


class FattreeCut(Enum):
    VERTICAL = ("v", "vertical", "Vertically partitioned")
    HORIZONTAL = ("h", "horizontal", "Horizontally partitioned")
    PODS = ("p", "pods", "Partitioned into pods")
    SPINES = ("s", "spines", "Partitioned into pods and individual spines")
    FULL = ("f", "full", "Fully partitioned")

    def __init__(self, short, long, desc):
        self.short = short
        self.long = long
        self.desc = desc

    @property
    def func(self):
        # cut function
        if self is FattreeCut.VERTICAL:
            return nodes_cut_vertically
        elif self is FattreeCut.HORIZONTAL:
            return nodes_cut_horizontally
        elif self is FattreeCut.PODS:
            return nodes_cut_pods
        elif self is FattreeCut.SPINES:
            return nodes_cut_spines
        elif self is FattreeCut.FULL:
            return nodes_cut_fully

    @staticmethod
    def from_str(s):
        for e in list(FattreeCut):
            if s == e.short or s == e.long:
                return e
        raise KeyError("cut not found")


class NodeGroup(Enum):
    """
    Core nodes are on the spine, edge nodes are ToR,
    and aggregation nodes are between core and edge nodes.
    None is used when nodes are not in fattree networks.
    """

    CORE = 0
    AGGREGATION = 1
    EDGE = 2
    NONE = 3

    @staticmethod
    def parse(name):
        if name == "core":
            return NodeGroup.CORE
        elif name == "aggregation":
            return NodeGroup.AGGREGATION
        elif name == "edge":
            return NodeGroup.EDGE
        else:
            return NodeGroup.NONE


class NetType(Enum):
    SP = 0
    FATPOL = 1
    NOTRANS = 2
    HIJACK = 3
    NONFAT = -1

    @staticmethod
    def from_filename(fname):
        if fname.startswith("sp"):
            return NetType.SP
        elif fname.startswith("fat"):
            return NetType.FATPOL
        else:
            return NetType.NONFAT


class NvFile:
    """
    Representation of an NV file's internal information.
    """

    def __init__(
        self,
        path: str,
        net_type: NetType,
        simulate: bool,
        dest: Optional[int],
        verbose: bool = False,
    ):
        self.path = path
        self.net = net_type
        self.dest = dest
        self.verbose = verbose
        with open(path) as f:
            self.mono = f.read()
        self.graph = construct_graph(self.mono, net_type)
        if self.verbose:
            print(self.print_graph())
        if simulate:
            self.sols = run_nv_simulate(self.path)
        else:
            self.sols = None

    def cut(self, cut_type):
        """
        Given the cut, generate a new NV file with partition and interface functions.
        """
        nodes = cut_type.func(self.graph, self.dest)
        if self.sols is not None:
            edges = get_cross_edges(self.graph, nodes, ranked=False)
        elif self.net is NetType.FATPOL and cut_type is FattreeCut.VERTICAL:
            # special case for handling vertical cuts
            edges = get_vertical_cross_edges(self.graph, nodes, self.dest)
        else:
            edges = get_cross_edges(self.graph, nodes, ranked=True)
        if self.verbose:
            print(nodes)
            print([e for e in edges])
        partition = write_partition_str(nodes)
        if self.sols is not None:
            interface = write_interface_from_sim(edges, self.sols)
        else:
            interface = write_interface_str(edges)
        # perform the decomposed transfer on the input side
        repl = (
            r"solution { init = init; trans = trans; merge = merge;"
            r" interface = interface; rtrans = trans }"
        )
        text = re.sub(r"solution {.*}", repl, self.mono)
        # put 'em all together
        return "\n".join([self._preamble(cut_type), text, partition, interface])

    def hijack(self, predicate, misconfigured):
        """
        Return a new NV file which represents hijacking the network.
        predicate describes the require predicate for the hijack.
        misconfigured controls whether the network policy should successfully
        block the hijack or if it should succeed.
        """
        # TODO: add a new hijacker node with edges to each of the spines
        # TODO: add symbolic for new hijacker node and a require predicate
        # TODO: modify init to initialize the hijacker
        # TODO: add transferBgp cases for hijacker edges, and add special hijack tag
        # TODO: add new assertion

    def _preamble(self, cut_type):
        """
        Return the string representation of the preamble.
        """
        vim_modeline = "(* vim: set syntax=ocaml: *)"
        file_info = f"(* {cut_type.desc} version of {os.path.basename(self.path)} *)"
        generated_by = "(* Automatically generated by gen_part_nv.py *)"
        return "\n".join([vim_modeline, file_info, generated_by])

    def print_graph(self):
        return str(self.graph)


def construct_graph(text, is_fattree):
    """
    Construct a digraph from the given edge and node information.
    """
    g = igraph.Graph(directed=True)
    nodes = find_nodes(text, is_fattree)
    for (v, grp) in nodes:
        g.add_vertex(g=grp)
    edges = find_edges(text, is_fattree)
    g.add_edges(edges)
    # add stable node numbering
    for v in g.vs():
        v["id"] = v.index
    return g


def find_edges(text, is_fattree):
    """Return the edges."""
    if is_fattree:
        pat = (
            r"(\d*)-(\d*); "
            r"\(\*(core|aggregation|edge)-\d*,Serial\d*"
            r" --> (core|aggregation|edge)-\d*,Serial\d*\*\)"
        )
    else:
        pat = r"(\d*)-(\d*); \(\*[\w/,]* --> [\w/,]*\*\)"
    prog = re.compile(pat)
    matches = prog.finditer(text)
    outputs = [(int(m.group(1)), int(m.group(2))) for m in matches]
    outputs.sort()
    return outputs


def find_nodes(text, net_type):
    """Return the nodes."""

    if net_type is not NetType.NONFAT:
        pat = r"(core|aggregation|edge)-\d*=(\d*)"

    else:
        pat = r"(\w+)(?:-\d*)?=(\d+)"
    prog = re.compile(pat)
    # find all nodes
    matches = prog.finditer(text)
    vertices = [(int(m.group(2)), NodeGroup.parse(m.group(1))) for m in matches]
    vertices.sort()
    return vertices


def write_partition_str(partitions):
    """
    Return the string representation of the partition function.
    """
    output = "let partition node = match node with\n"
    for i, nodes in enumerate(partitions):
        output += "\n".join([f"  | {node}n -> {i}" for node in nodes]) + "\n"
    return output


def write_interface_str(edges):
    """
    Return the string representation of the interface function.
    """
    output = "let interface edge x ="
    output += """
  let hasOnlyBgp =
    x.selected = Some 3u2 && (match x.bgp with
      | Some b -> true
      | None -> false)
  in"""
    output += "\n  match edge with\n"
    for (start, end) in edges:
        output += f"  | {start}~{end} -> hasOnlyBgp\n"
    output += f"  | _ -> true\n"
    return output


def get_part_fname(nvfile, cut, simulate):
    """
    Return the name of the partition file for the corresponding nv file,
    and the network type.
    """
    spdir, spname = os.path.split(nvfile)
    root, nvext = os.path.splitext(spname)
    net_type = NetType.from_filename(root)
    # mark simulated solutions with an x for exact
    sim = "-x" if simulate else ""
    prefix = f"{root}-{cut.short}{sim}"
    partfile = os.path.join(spdir, prefix + nvext)
    suffix = 1
    # don't overwrite an existing path: instead, create a new file
    while os.path.exists(partfile):
        partfile = os.path.join(spdir, prefix + str(suffix) + nvext)
        suffix += 1
    return partfile, net_type


def nodes_cut_fully(graph, dest):
    """
    Return the nodes divided up fully into separate partitions.
    Order is established by BFS.
    """
    return [[v["id"]] for v in graph.bfsiter(dest)]


def nodes_cut_spines(graph, dest):
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


def nodes_cut_pods(graph, dest):
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


def nodes_cut_horizontally(graph, dest):
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
    return dest_pod, spines, nondest_pods


def nodes_cut_vertically(graph, dest):
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
        return group1, group2
    else:
        return group2, group1


def get_cross_edges(graph, partitions, ranked=False):
    """
    Get the edges in the network which go between partitions.
    If ranked is True, only include edges which go from lower-ranked partitions
    to higher-ranked partitions.
    These edges are used to determine the interface functions.
    """
    # construct a map of nodes to their partitions
    n_parts = {node: i for (i, part) in enumerate(partitions) for node in part}

    def edge_predicate(e):
        src = n_parts[e.source]
        tgt = n_parts[e.target]
        return (ranked and src < tgt) or (not ranked and src != tgt)

    return [e.tuple for e in graph.es if edge_predicate(e)]


def get_vertical_cross_edges(graph, partitions, dest):
    all_cross = get_cross_edges(graph, partitions, ranked=True)
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


def run_nv_simulate(path):
    """ Run nv's simulation tool and capture its output. """
    nvpath = os.path.join(os.getcwd(), "nv")
    if not os.path.exists(nvpath):
        print("Did not find 'nv' executable in the current working directory")
        sys.exit(1)
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


def write_interface_from_sim(edges, solution):
    """
    Write an interface string based on the given simulation.
    """
    output = "let interface edge a =\n  match edge with\n"
    for (start, end) in edges:
        sol = solution[start]
        output += f"  | {start}~{end} -> a = {sol}\n"
    return output


# TODO: make the dest optional if simulate is True
def gen_part_nv(nvfile, dest, cut, simulate=True, verbose=False):
    """Generate the partition file."""
    part, net_type = get_part_fname(nvfile, cut, simulate)
    if verbose:
        print("Outfile: " + part)
    nv = NvFile(nvfile, net_type, simulate, dest, verbose)
    partitioned = nv.cut(cut)
    with open(part) as outfile:
        outfile.write(partitioned)
    print(f"Saved network to {part}")


def print_graph(nvfile):
    """Print the associated graph for the given NV file."""
    _, spname = os.path.split(nvfile)
    root, _ = os.path.splitext(spname)
    net_type = NetType.from_filename(root)
    nv = NvFile(nvfile, net_type, False, None)
    print(nv.print_graph())
    # adj = graph.get_adjlist(mode="all")
    # assert all([len(l) % 2 == 0 for l in adj])


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
    parser.add_argument(
        "-c",
        "--cuts",
        required=True,
        nargs="+",
        choices=CUTS,
        help="types of cut across the network topology",
    )
    parser.add_argument(
        "-s",
        "--simulate",
        action="store_true",
        help="generate interface by simulating the given benchmark",
    )
    parser.add_argument(
        "-v", "--verbose", action="store_true", help="increase verbosity"
    )
    parser.add_argument(
        "-p",
        "--print",
        action="store_true",
        help="print topology info instead of generating partition",
    )
    return parser


def main():
    args = parser().parse_args()
    for (file, dest) in args.files.items():
        if args.print:
            print_graph(file)
        else:
            for cut in args.cuts:
                gen_part_nv(file, dest, FattreeCut.from_str(cut), verbose=args.verbose)


if __name__ == "__main__":
    main()
