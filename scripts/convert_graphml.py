#!/usr/bin/env python3
"""
Load a GraphML file and convert it to an NV topology.
"""
import igraph
import sys


def load_graph(graphml_path: str) -> igraph.Graph:
    g = igraph.Graph.Read_GraphML(graphml_path)
    g.to_directed()
    # if any multi-edges are in the graph, combine them
    g.simplify(combine_edges=dict(id=lambda edges: ", ".join(edges)))
    return g


def into_topology_str(g: igraph.Graph) -> str:
    """
    Convert the given digraph into a string listing nodes
    and edges of the network.
    """
    nodes = f"let nodes = {g.vcount()}"
    es = []
    for e in g.es:
        u, v = e.vertex_tuple
        s = f"  {u.index}-{v.index}; (* {e['id']}: {u['label']},{int(u['id'])} --> {v['label']},{int(v['id'])} *)"
        es.append(s)
    edges = "let edges = {{\n{}\n}}".format("\n".join(es))
    return "\n\n".join([nodes, edges])


if __name__ == "__main__":
    g = load_graph(sys.argv[1])
    print(into_topology_str(g))
