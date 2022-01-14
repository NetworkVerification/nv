#!/usr/bin/env python3
# Generator scripts for NV benchmarks.
# Supplementary tools to run nvgen and generate many benchmarks at once.
from dataclasses import dataclass
from enum import Enum
from typing import Optional
import os
from pathlib import Path
import subprocess
import sys

import topzoo
import igraph


def is_int(s):
    try:
        int(s)
        return True
    except ValueError:
        return False


def is_float(s):
    try:
        float(s)
        return True
    except ValueError:
        return False


class Topology(str):
    def __init__(self, s):
        """
        Create a new topology from a string.
        Topology strings should be a keyword, followed by one or more underscores
        separating numbers.
        """
        self.s = s
        match s.split("_"):
            case ["fat", k] if is_int(k):
                self.top = "fat"
            case ["star", x] if is_int(x):
                self.top = "star"
            case ["mesh", x] if is_int(x):
                self.top = "mesh"
            case ["ring", x] if is_int(x):
                self.top = "ring"
            case ["rand", n, p] if is_int(n) and is_float(p):
                self.top = "rand"
            case _:
                raise ValueError("Invalid argument given to Topology.__init__()")

    @staticmethod
    def rand(n: int, p: float):
        t = Topology(f"rand_{n}_{p}")
        return t


class NvgenOperation(Enum):
    TOPOLOGY = "topology"
    FT = "ft"
    MAINTENANCE = "maintenance"
    NOTRANS = "notrans"
    CUT = "cut"
    HIJACK = "hijack"


@dataclass
class NvgenArgs:
    inputfile: os.PathLike
    operation: NvgenOperation
    verbose: bool = False
    outfile: Optional[str] = None
    destination: Optional[int] = None
    topology: Optional[Topology] = None

    def to_list(self) -> list[str]:
        """Convert the arguments into a list of strings."""
        args: list[str] = []
        if self.verbose:
            args += ["-v"]
        if self.outfile:
            args += ["-o", self.outfile]
        if self.destination:
            args += ["-d", str(self.destination)]
        if self.topology:
            args += ["-t", self.topology]
        args += [self.inputfile, self.operation.value]
        return args


def run_nvgen(*cmd_args: NvgenArgs):
    """
    Run nvgen with the given arguments.
    Print anything written to stdout.
    """
    nvgenpath = os.path.join(os.getcwd(), "nvgen")
    if not os.path.exists(nvgenpath):
        print("Did not find 'nvgen' executable in the current working directory")
        sys.exit(1)
    for args in cmd_args:
        try:
            proc = subprocess.run(
                [nvgenpath] + args.to_list(), check=True, capture_output=True
            )
            print(proc.stdout)
            if args.outfile:
                print(f"Generated {args.outfile}")
        except subprocess.CalledProcessError as exn:
            print(exn)
            continue


def gen_maintenance_benchmarks(benchmarks: list[tuple[os.PathLike, int]]):
    def outputf(path: os.PathLike):
        hd, tl = os.path.split(path)
        # generate the new maintenance version of the fatXPol benchmark
        return os.path.join(hd, tl.replace("sp", "maintenance"))

    args = [
        NvgenArgs(
            inputf,
            NvgenOperation.MAINTENANCE,
            outfile=outputf(inputf),
            destination=dest,
        )
        for (inputf, dest) in benchmarks
    ]
    run_nvgen(*args)


def gen_rand_benchmarks(
    benchmarks: list[tuple[int, float]],
    outpath: os.PathLike,
):
    for n, p in benchmarks:
        g = igraph.Graph.Erdos_Renyi(n, p=p, directed=True, loops=False)
        g.vs["label"] = [None] * g.vcount()
        top = Topology.rand(n, p)
        nvfile = topzoo.to_nv(top, g, dest=0)
        outfile = os.path.join(outpath, nvfile.name)
        with open(outfile, "w") as output:
            output.write(str(nvfile))


if __name__ == "__main__":
    match sys.argv[1:]:
        case ["rand", outpath, start, stop]:
            n_p = [(2 ** k, 2 ** (2 - k)) for k in range(int(start), int(stop))]
            gen_rand_benchmarks(n_p, Path(outpath))
        case ["maintenance", *directories]:
            pass
        case _:
            print("Invalid arguments given.")
