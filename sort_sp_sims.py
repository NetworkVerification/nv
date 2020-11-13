#!/usr/bin/python
import re
import subprocess
import sys

# get the solutions to the sp.nv program (for use when writing invariants)


def parse_sols(s):
    """Convert the solution print-out text into a succinct key-value pair."""
    pat = r"Node (\d+)\n-*\n{\s*bgp=\s*Some\({\s*aslen= (\d*)u32;.*"
    miter = re.finditer(pat, s, flags=re.M)
    return [m.group(1, 2) for m in miter]


def sort_sols(s):
    """Read in the output of simulation and return a sorted list of solutions."""
    sols = parse_sols(s)
    # sort the tuples by the second item
    sorted_sols = sorted(sols, key=lambda i: i[1])
    dest = [n for (n, v) in sorted_sols if v == "0"]
    pod = [n for (n, v) in sorted_sols if v == "1"]
    print("Destination (0 hops): " + dest[0])


def run_nv(bench):
    """Run the given NV benchmark and return its output."""
    proc = subprocess.run(["nv", "-s", "-v", bench], capture_output=True, text=True)
    sort_sols(proc.stdout)


if __name__ == "__main__":
    BENCH = sys.argv[1]
    run_nv(BENCH)
