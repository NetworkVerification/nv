"""
Utilities for generating Topology Zoo benchmarks.
"""
from enum import Enum
from typing import Iterable, Literal
import igraph
import os
import sys
from utils import Bgp


class ASRelationship(Enum):
    CUST_PROV = "cust_prov"
    PEER_PEER = "peer_peer"
    PROV_CUST = "prov_cust"


class NvFile:
    def __init__(self, name):
        self.name = name
        self.types = []
        self.symbolics = []
        self.requires = []
        self.consts = []
        self.funcs = []
        self.sols = []
        self.asserts = []

    def add_type(self, tname, ty_exp):
        self.types.append(f"type {tname} = {ty_exp}")

    def add_topology(self, g: igraph.Graph):
        """
        Add the topology, parsed from the given Graph.
        The graph should have a label attribute for each node,
        and optionally an id str attribute for each edge.
        """

        def node_to_name(v: igraph.Vertex):
            return f"{v['label']},{v.index}"

        nodes = f"let nodes = {g.vcount()}"
        self.consts.append(nodes)
        # add the node mapping to the end of the file
        node_list = comment(
            "{" + ", ".join([f"{node_to_name(v)}={v.index}" for v in g.vs]) + "}"
        )
        self.asserts.append(node_list)
        es = []
        for e in g.es:
            u, v = e.vertex_tuple
            if "id" in e.attribute_names():
                s = f"  {u.index}-{v.index}; (* {e['id']}: {node_to_name(u)} --> {node_to_name(v)} *)"
            else:
                s = f"  {u.index}-{v.index}; (* {node_to_name(u)} --> {node_to_name(v)} *)"
            es.append(s)
        edges = "let edges = {{\n{}\n}}".format("\n".join(es))
        self.consts.append(edges)

    def add_symb(self, name, ty):
        self.symbolics.append(f"symbolic {name} : {ty}")

    def add_req(self, exp):
        self.requires.append(f"require {exp}")

    def add_let(self, fname, args, fbody):
        if len(args) > 0:
            argstr = " ".join(args)
            self.funcs.append(f"let {fname} {argstr} = {fbody}")
        else:
            self.consts.append(f"let {fname} = {fbody}")

    def add_solution(self, var):
        self.sols.append(
            f"let {var} = solution {{ init = init; trans = trans; merge = merge; }}"
        )

    def add_assert(self, exp):
        self.asserts.append(f"assert {exp}")

    def __str__(self):
        s = ""
        s += comment(f"Generated by {os.path.basename(__file__)}") + "\n\n"
        s += "\n\n".join(
            self.types
            + self.consts
            + self.symbolics
            + self.requires
            + self.funcs
            + self.sols
            + self.asserts
        )
        return s


def from_relns(relns_file: str) -> igraph.Graph:
    """
    Import a topology and relationships from a relns.txt file.
    The file should be evaluated as a Python dictionary,
    where the keys are tuple[str,str] and the values are one of
    'prov_cust', 'peer_peer' and 'cust_prov'.
    Returns a directed Graph with nodes labelled by their string names,
    and edges labelled by their relationships.
    """
    with open(relns_file, "r") as relns_text:
        t = relns_text.read()
        relns: dict[tuple[str, str], str] = eval(t)
    # edges as labelled node pairs
    labelled_edges = relns.keys()
    # get all node labels
    node_labels = set(x for l in [[u, v] for (u, v) in labelled_edges] for x in l)
    # map labels to node numbers
    label_to_node = {name: i for (i, name) in enumerate(node_labels)}
    # edges to edge labels
    edge_labels = {
        (label_to_node[u], label_to_node[v]): ASRelationship(rel)
        for ((u, v), rel) in relns.items()
    }
    return igraph.Graph(
        len(node_labels),
        list(edge_labels.keys()),
        directed=True,
        vertex_attrs=dict(label=list(label_to_node.keys())),
        edge_attrs=dict(rel=list(edge_labels.values())),
    )


def from_graphml(graphml_file: str) -> igraph.Graph:
    """Import a network topology from a GraphML file."""
    g = igraph.Graph.Read_GraphML(graphml_file)
    g.to_directed()
    # if any multi-edges are in the graph, combine them
    g.simplify(combine_edges=dict(id=lambda edges: ", ".join(edges)))
    return g


def comment(s: str) -> str:
    """Return an OCaml comment containing the given string s."""
    return "(* " + s + " *)"


def pattern(x):
    if isinstance(x, tuple) and len(x) == 2:
        return f"{x[0]}~{x[1]}"
    else:
        return str(x)


def dict_to_match(d: dict, exp):
    branches = "\n".join([f"| {pattern(pat)} -> {body}" for (pat, body) in d.items()])
    return f"match {exp} with\n{branches}"


def undirected(directed: Iterable[tuple[int, int]]):
    """Convert a list of directed edges to undirected edges."""
    return [(u, v) for (u, v) in directed if u < v]


def node_to_int(nodes: int, node_exp) -> str:
    """Create a match statement mapping nodes to integers."""
    return dict_to_match({f"{n}n": n for n in range(nodes)}, node_exp)


def stubs(graph: igraph.Graph) -> list[int]:
    """Return the list of stub nodes."""
    # start from every node, drop any node that is ever a peer or a provider
    stubs = set(range(0, graph.vcount()))
    for e in graph.es:
        u, v = e.tuple
        match e["rel"]:
            case ASRelationship.CUST_PROV:
                stubs.discard(v)
            case ASRelationship.PEER_PEER:
                stubs.discard(u)
                stubs.discard(v)
            case ASRelationship.PROV_CUST:
                stubs.discard(u)
    return list(stubs)


def add_policy(nv: NvFile, notrans: bool):
    # merge
    nv.funcs.append(
        r"""let pickOption f x y =
  match (x,y) with
  | (None, None) -> None
  | (None, Some _) -> y  | (Some _, None) -> x
  | (Some a, Some b) -> Some (f a b)

let betterBgp b1 b2 =
  if b1.lp > b2.lp then b1
  else if b2.lp > b1.lp then b2
  else if b1.aslen < b2.aslen then b1
  else if b2.aslen < b1.aslen then b2  else if b1.med >= b2.med then b1 else b2

let mergeBgp x y = pickOption betterBgp x y

let merge n x y = mergeBgp x y"""
    )

    # transfer
    if notrans:
        nv.funcs.append(
            r"""(* We add community tags to designate providers, peers and customers,
* and use these tags to adjust local preference.
* We also need to identify when an edge is to a provider or a peer,
* in which case if the route is tagged as from a customer then it
* should be dropped.
* The relationship(a~b) edge function returns:
* - cust_prov if a is a customer of b (b is a provider for a)
* - peer_peer if a is a peer of b (should be symmetric)
* - prov_cust if a is a provider for b (b is a customer of a)
* A node v will only advertise a route from its neighbor u to another neighbor w according to the following rules:
* if relationship(uv) = customer, v will advertise the route to w;
* if relationship(uv) = peer or relationship(uv) = prov, v will only advertise the route to w if relationship(vw) = cust
*)
let transferBgp e x =
match x with
| None -> None
| Some b -> (
    (* enforce no transit: if the route is neither from a customer nor to a customer, then drop it;
    * don't use !(b.comms[cust_prov]) since by default b.comms starts empty
    *)
    if (b.comms[peer_peer] || b.comms[prov_cust]) && !(relationship e = prov_cust) then None else
    (* update LP *)
    let lp = if (relationship e = cust_prov) then 200
        else if (relationship e = peer_peer) then 100
        else 0
    in
    (* update comms: mark the source of the message and remove old relationship tags *)
    let comms = if (relationship e = cust_prov) then b.comms[cust_prov := true][peer_peer := false][prov_cust := false]
        else if (relationship e = peer_peer) then b.comms[peer_peer := true][cust_prov := false][prov_cust := false]
        else b.comms[prov_cust := true][cust_prov := false][peer_peer := false]
    in
    let b = {b with comms = comms; aslen = b.aslen + 1; lp = lp} in
    Some b
)

let trans e x = transferBgp e x"""
        )
    else:
        nv.funcs.append(
            r"""(* Simple shortest-path routing. *)
let transferBgp e x =
  match x with
  | None -> None
  | Some b -> Some {b with aslen = b.aslen + 1}

let trans e x = transferBgp e x"""
        )
    nv.add_let("assert_node", ["u", "v"], "match v with | None -> false | _ -> true")
    nv.add_solution("sol")
    nv.add_assert("foldNodes (fun u v acc -> acc && assert_node u v) sol true")


def to_nv(
    net_name: str, graph: igraph.Graph, dest: int | Literal["symbolic"]
) -> NvFile:
    """
    Create an NV file.
    If business_rel is not None, the policy should enforce no-transit; otherwise, it should
    be a shortest-paths policy.
    """
    f = NvFile(f"{net_name}.nv")
    f.types.append(Bgp.TypeDeclaration())
    f.add_type("attribute", "option[bgpType]")

    f.add_topology(graph)
    no_trans = "rel" in graph.edge_attributes()

    if no_trans:
        relp_body = dict_to_match({e.tuple: e["rel"] for e in graph.es}, "e")
        f.add_let("cust_prov", [], 0)
        f.add_let("peer_peer", [], 1)
        f.add_let("prov_cust", [], 2)
        f.add_let("relationship", ["e"], relp_body)

    # init
    if dest == "symbolic":
        f.add_symb("d", "int")
        if no_trans:
            # require that d is a stub
            allowed_nodes = " || ".join([f"d = {v}" for v in stubs(graph)])
            f.add_req(allowed_nodes)
        f.add_req(f"d < {graph.vcount()}")
        f.add_let("node_to_int", ["n"], node_to_int(graph.vcount(), "n"))
        cond = "(node_to_int n) = d"
    else:
        cond = f"n = {dest}n"
    bgp = Bgp(0)
    f.funcs.append(f"let init n = if {cond} then Some {bgp} else None")
    add_policy(f, no_trans)
    return f


def to_hgr(graph):
    """
    Return a string representation of an hgr hypergraph file.
    Requires converting the given graph to be undirected (if it isn't already).
    """
    graph.to_undirected()
    edges = graph.get_edgelist()
    nodes = graph.vcount()
    preamble = (
        f"% generated from {os.path.basename(__file__)}\n"
        "% number of edges; number of vertices\n"
        f"% note vertex numbering starts from 1, so 0 is remapped to {nodes}"
    )
    # remap 0 to the max node to start numbering from 1
    edges = [(u if u > 0 else nodes, v if v > 0 else nodes) for (u, v) in edges]
    edge_list = "\n".join([f"{u} {v}" for (u, v) in edges])
    totals = f"{len(edges)} {nodes}"
    return "\n".join([preamble, totals, edge_list])


def to_dot(name, graph):
    graph.to_undirected()
    preamble = f"// generated from {os.path.basename(__file__)}"
    edge_list = "\n".join([f"  {u} -- {v};" for (u, v) in graph.get_edgelist()])
    return "\n".join([preamble, f"graph {name} {{", edge_list, "}"])


if __name__ == "__main__":
    input_file = sys.argv[1]
    if input_file == "-h" or input_file == "--help":
        print("Usage: topzoo.py [graphml or relns file] [nv|hgr|dot]")
        exit(0)
    net_dir, net_file = os.path.split(input_file)
    if net_file.endswith(".graphml"):
        net_name = net_file.removesuffix(".graphml")
        graph = from_graphml(input_file)
    elif net_file.endswith("_relns.txt"):
        # get the name of the network from the relns file
        net_name = net_file.removesuffix("_relns.txt")
        graph = from_relns(input_file)
    else:
        raise ValueError(
            "Expected first argument to be a .graphml file or a _relns.txt file."
        )
    match sys.argv[2]:
        case "nv":
            match sys.argv[3:]:
                case ["-s", *_] | ["--symbolic", *_]:
                    dest = "symbolic"
                case ["-d", d, *_] | ["--dest", d, *_]:
                    dest = int(d)
                case _:
                    raise ValueError("No nv destination node provided!")
            print(to_nv(net_name, graph, dest))
        case "hgr":
            print(to_hgr(graph))
        case "dot":
            print(to_dot(net_name, graph))
        case _:
            print("Usage: topzoo.py [graphml or relns file] [nv|hgr|dot]")
