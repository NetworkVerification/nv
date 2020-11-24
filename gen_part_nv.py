#!/usr/bin/env python3
"""
gen_part_nv.py [spfile]
A module for generating spX-part.nv fileoutput from spX.nv files.
"""
import sys
import os
import re

# used for constructing the graph (doing it again in Python seems silly, but it's easy!)
import igraph

# Orientation of partition
HORIZONTAL = True
VERTICAL = False

# Group
# Core nodes are on the spine, edge nodes are ToR, and aggregation nodes are between core and edge nodes
CORE = 0
AGGREGATION = 1
EDGE = 2


def cross_partition(e):
    (u, v) = e.vertex_tuple
    return (u["g"] == CORE and v["g"] == AGGREGATION) or (
        u["g"] == AGGREGATION and v["g"] == CORE
    )


def to_grp(name):
    if name == "core":
        return CORE
    elif name == "aggregation":
        return AGGREGATION
    elif name == "edge":
        return EDGE
    else:
        raise Exception("group name not recognized!")


def construct_graph(text):
    """
    Construct a digraph from the given edge and node information.
    """
    g = igraph.Graph(directed=True)
    for (v, grp) in find_nodes(text):
        g.add_vertex(g=grp)
    g.add_edges(find_edges(text))
    # add stable node numbering
    for v in g.vs:
        v["id"] = v.index
    return g


def find_edges(text):
    """Return the edges."""
    prog = re.compile(
        r"(\d*)-(\d*); "
        r"\(\*(core|aggregation|edge)-\d*,Serial\d* --> (core|aggregation|edge)-\d*,Serial\d*\*\)"
    )
    matches = prog.finditer(text)
    outputs = [(int(match.group(1)), int(match.group(2))) for match in matches]
    outputs.sort()
    return outputs


def find_nodes(text):
    """Return the nodes."""
    prog = re.compile(r"(core|aggregation|edge)-\d*=(\d*)")
    # find all nodes
    matches = prog.finditer(text)
    vertices = [(int(match.group(2)), to_grp(match.group(1))) for match in matches]
    vertices.sort()
    return vertices


def write_preamble(spname, orientation=HORIZONTAL):
    """
    Return the string representation of the preamble.
    """
    vim_modeline = "(* vim: set syntax=ocaml: *)"
    oriented = "Vertically" if orientation else "Horizontally"
    file_info = f"(* {oriented} partitioned version of {spname} *)"
    generated_by = "(* Automatically generated by gen_part_nv.py *)"
    include_utils = 'include "../../../examples/utils.nv"'
    return "\n".join([vim_modeline, file_info, generated_by, include_utils])


def write_partition_str(partitions):
    """
    Return the string representation of the partition function.
    """
    output = "let partition node = match node with\n"
    for i, nodes in enumerate(partitions):
        output += "\n".join([f"  | {node}n -> {i}u8" for node in nodes]) + "\n"
    # output += "\n  | _ -> 1u8\n"
    return output


def write_interface_str(fwd_cross, back_cross):
    """
    Return the string representation of the interface function.
    """
    output = "let interface edge =\n"
    common_block = """match x with
      | { connected = c; static = s; ospf = o; bgp = b; selected = sel } ->
        c = None && s = None && o = None"""
    anyb = """  let any x = true
    in
    """
    nbb = f"""let nothingButBgp x =
      {common_block}
    in
    """
    hob = f"""let hasOnlyBgp x =
      {common_block} && isSome b && sel = Some 3u2
    in
    """
    output += anyb + nbb + hob
    output += "match edge with\n"
    for (start, end) in fwd_cross:
        output += f"  | {start}~{end} -> Some hasOnlyBgp\n"
    for (start, end) in back_cross:
        output += f"  | {start}~{end} -> Some any\n"
    output += "  | _ -> None\n"
    return output


def get_part_fname(spfile, orientation=HORIZONTAL):
    """Return the name of the partition file for the corresponding spX.nv file."""
    spdir, spname = os.path.split(spfile)
    root, nvext = os.path.splitext(spname)
    part_suffix = "-part" if orientation else "-vpart"
    partfile = os.path.join(spdir, root + part_suffix + nvext)
    suffix = 1
    # don't overwrite an existing path: instead, create a new file
    while os.path.exists(partfile):
        partfile = os.path.join(spdir, root + part_suffix + str(suffix) + nvext)
        suffix += 1
    return partfile


def nodes_cut_horizontally(graph, dest):
    """
    Return the nodes divided up such that the destination's pod
    is in one partition, the spine nodes are in another and the
    other pod nodes are in a third.
    """
    podgraph = graph.subgraph(graph.vs.select(g_ne=CORE))
    pods = podgraph.decompose()
    dest_pod = []
    nondest_pods = []
    for pod in pods:
        if dest in pod.vs["id"]:
            dest_pod = [v["id"] for v in pod.vs]
        else:
            nondest_pods += [v["id"] for v in pod.vs]
    spines = [v["id"] for v in graph.vs.select(g_eq=CORE)]
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
    spines = [v for v in graph.vs.select(g_eq=CORE)]
    half_spines = spines[: (len(spines) // 2)]
    aggs = [v for v in graph.vs.select(g_eq=AGGREGATION)]
    half_aggs = aggs[: (len(aggs) // 2)]
    # use a set so as not to add twice
    pods = set()
    for v in half_aggs:
        pods.add(v.index)
        for u in v.neighbors():
            if u["g"] == EDGE:
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


def validate(spine_nodes, cross_edges):
    """Validate that every cross edge goes to or from a spine node."""
    for (start, end) in cross_edges:
        if start not in spine_nodes and end not in spine_nodes:
            print(
                f"Warning: Edge {start},{end} does not appear to connect to the spine!"
            )


def gen_nosol_nv(sptext):
    """
    Drop the solution declarations and any assertions using it from the sptext.
    Return the new sptext and the assertions found.
    """
    prog = re.compile(r"^let (\w*) = solution .*$")
    varnames = [(m.group(1), m.start(), m.end()) for m in prog.finditer(sptext)]
    # find any assertion lines using these variable names
    prog2 = re.compile(r"^assert .*$")
    assertions = [(m.start(), m.end()) for m in prog.finditer(sptext)]
    text = ""
    for (_, start, end) in varnames:
        text += sptext[:start]
    return text


def split_prefooter(sptext):
    prog = re.compile(r"\(\* {((edge|core|aggregation)-\d+=\d+,?\s*)*}\*\)")
    match = prog.search(sptext)
    end = match.end()
    return (sptext[: end + 1], sptext[end + 1 :])


def gen_part_nv(spfile, dest, orientation=HORIZONTAL, verbose=False):
    """Generate the partition file."""
    part = get_part_fname(spfile, orientation)
    if verbose:
        print("Outfile: " + part)
    with open(spfile, "r") as inputfile:
        sptext = inputfile.read()
    # compute the graph topology
    graph = construct_graph(sptext)
    if verbose:
        print(str(graph))
    # sys.exit(0)
    # get the three parts
    # include_sp = f'include "{os.path.basename(spfile)}"'
    preamble = write_preamble(os.path.basename(spfile))
    include_sp, footer = split_prefooter(sptext)
    if orientation == HORIZONTAL:
        nodes = nodes_cut_horizontally(graph, dest)
        # cross_edges = [e.tuple for e in graph.es if cross_partition(e)]
        fwd = lambda e: (e.source in nodes[0] and e.target in nodes[1]) or (
            e.source in nodes[1] and e.target in nodes[2]
        )
        fwd_cross = [e.tuple for e in graph.es if cross_partition(e) and fwd(e)]
        back_cross = [e.tuple for e in graph.es if cross_partition(e) and not fwd(e)]
    else:
        nodes = nodes_cut_vertically(graph, dest)
        cross_edges = [
            e.tuple for e in graph.es if (e.source in nodes != e.target in nodes)
        ]
        fwd = lambda e: e.source in nodes[0] and e.target in nodes[1]
        # FIXME: something seems wrong with these
        fwd_cross = [e.tuple for e in cross_edges and fwd(e)]
        back_cross = [e.tuple for e in cross_edges and not fwd(e)]
    # validate spine and cross edges
    validate(nodes[1], fwd_cross + back_cross)
    if verbose:
        print(nodes)
        print(cross_edges)
    partition = write_partition_str(nodes)
    interface = write_interface_str(fwd_cross, back_cross)
    # perform the decomposed transfer on the input side
    repl = r"solution { init = init; trans = trans; merge = merge; interface = interface; rtrans = trans }"
    solution = re.sub(r"solution {.*}", repl, footer)
    # solution = "\nlet sol = solution { init = init; trans = trans; merge = merge; interface = interface; rtrans = trans }"
    # put 'em all together
    output = "\n".join([preamble, include_sp, partition, interface, solution])
    with open(part, "w") as outfile:
        outfile.write(output)
    print(f"Saved network to {part}")


if __name__ == "__main__":
    INPUT = sys.argv[1]
    ORIENT = sys.argv[2]
    DEST = sys.argv[3]
    if ORIENT == "h":
        gen_part_nv(INPUT, int(DEST), HORIZONTAL)
    elif ORIENT == "v":
        gen_part_nv(INPUT, int(DEST), VERTICAL)
    else:
        print("Invalid orientation given!")
