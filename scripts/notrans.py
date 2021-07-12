#!/usr/bin/env python3

import sys
import gen_part_nv
import igraph


def infer_relationships(graph: igraph.Graph):
    """
    Return a copy of the given undirected graph
    as a directed graph G' with edges removed according to
    our guesses as what relationships might exist.
    We use the following procedure to delete edges from G':
    1. If a node u has a single undirected edge with v, delete vu.
    2. If a node v has directed edges uv, vw and wv, delete wv.
    3. If a node v has directed edges uv, vu and wv, vw, but
       u or w have directed edges into them, delete uv and wv.
    """
    g = graph.copy()
    g.to_directed()
    # alternate idea: degree hierarchy
    # if my neighbor has a higher degree than I do, delete his edge to me
    # for u in g.vs:
    #     for v in g.neighbors(u, mode="out"):
    #         if g.degree(v) > g.degree(u):
    #             g.delete_edges([(v, u)])
    # round 1: isolate stubs
    for v in g.vs.select(_degree_eq=2):
        neighbor = g.predecessors(v)[0]
        g.delete_edges([(neighbor, v)])
    # round 2: chain stubs
    d3 = g.vs.select(_degree_eq=3)
    while len(d3) > 0:
        for v in d3:
            # print(g.neighbors(v))
            u, w = g.predecessors(v)
            if (v, u) not in g.es:
                g.delete_edges([(w, v)])
            elif (v, w) not in g.es:
                g.delete_edges([(u, v)])
            else:
                raise Exception("Unexpected edge missing")
        d3 = g.vs.select(_degree_eq=3)

    return g


def main(f):
    with open(f) as nvfile:
        text = nvfile.read()
    graph = gen_part_nv.construct_graph(text)
    gprime = infer_relationships(graph)
    edges = "\n".join([f"  {e.source} -> {e.target};" for e in gprime.es])
    print(f"// edges: {graph.ecount()} --> {gprime.ecount()}")
    print("digraph USCarrier {\n" + edges + "\n}")


if __name__ == "__main__":
    main(sys.argv[1])
