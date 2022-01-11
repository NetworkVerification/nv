#!/usr/bin/env python3
# Script to infer no-transit relationships based on a network's graph.
# Not in active use.

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


def sort_by_degree(graph: igraph.Graph):
    """Return the vertices sorted by degree."""
    vertices = [(v["id"], graph.predecessors(v)) for v in graph.vs]
    vertices.sort(key=lambda x: len(x[1]))
    return vertices


def main(f):
    with open(f) as nvfile:
        text = nvfile.read()
    graph = gen_part_nv.construct_graph(text)
    vs = sort_by_degree(graph)
    last = 0
    seen = dict()
    for (v, d) in vs:
        if last < len(d):
            print(f"(* Nodes of degree {len(d)} *)")
        already_seen = (
            [f"{v} at {seen[v]}"]
            if v in seen
            else [] + [f"{u} at {seen[u]}" for u in d if u in seen]
        )
        print(
            f"(* {v} *) "
            + " ".join([f"| {u}~{v} -> peer | {v}~{u} -> peer" for u in d])
            + (
                ""
                if len(already_seen) == 0
                else f" (* seen: {'; '.join(already_seen)} *)"
            )
        )
        last = len(d)
        seen[v] = len(d)
        seen.update({u: len(d) for u in d})
    # gprime = infer_relationships(graph)
    # edges = "\n".join([f"  {e.source} -> {e.target};" for e in gprime.es])
    # print(f"// edges: {graph.ecount()} --> {gprime.ecount()}")
    # print("digraph USCarrier {\n" + edges + "\n}")


if __name__ == "__main__":
    main(sys.argv[1])
