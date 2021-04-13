#!/usr/bin/python
import re
import subprocess
import sys
from gen_part_nv import run_nv_simulate

# get the solutions to the sp.nv program (for use when writing invariants)


def parse_sols(sols):
    """Extract the BGP route length from the solution text."""
    new_sols = dict()
    for (k, v) in sols.items():
        pat = r"{\s*bgp=\s*Some\({\s*aslen= (\d*)u32;.*"
        new_sols[k] = int(re.sub(pat, r"\1", v))
    return new_sols


def sort_sols(sols):
    """
    Read in the output of simulation and return a sorted list of solutions.
    """
    sols = [p for p in parse_sols(sols).items()]
    # sort the tuples by the second item
    sorted_sols = sorted(sols, key=lambda i: i[1])
    dest = [n for (n, v) in sorted_sols if v == "0"]
    # pod = [n for (n, v) in sorted_sols if v == "1"]
    print("Destination (0 hops): " + dest[0])
    for (n, v) in sorted_sols:
        print("%s: %d" % (n, v))


def run_nv(bench):
    """Run the given NV benchmark and return its output."""
    args = ["nv", "-s", "-v", bench]
    proc = subprocess.run(args, capture_output=True, text=True)
    sort_sols(proc.stdout)


if __name__ == "__main__":
    BENCH = sys.argv[1]
    sols = run_nv_simulate(BENCH)
    sort_sols(sols)
