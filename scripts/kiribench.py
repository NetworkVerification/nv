#!/usr/bin/env python3
"""
Main module to generate, run and tabulate the Kirigami benchmarks.
"""

import argparse
import os
import re
import subprocess
import sys
from datetime import datetime
from gen_part_nv import gen_part_nv, run_nv_simulate, FattreeCut
from tabulator import (
    run_trials_sync,
    run_trials_parallel,
    write_csv,
)

BENCHMARKS = {
    # Single Prefix
    "sp": ("benchmarks/SinglePrefix/FAT{0}/", "sp{0}"),
    "sp_fatpol": ("benchmarks/SinglePrefix/FAT{0}", "fat{0}Pol"),
    "sp_topzoo": ("benchmarks/SinglePrefix/TopologyZoo", "USCarrier"),
    "ap_fatpol": ("benchmarks/AllPrefixes/FAT{0}", "fat{0}Pol"),
    "ap_topzoo": ("benchmarks/AllPrefixes/TopologyZoo", "USCarrier"),
    "sp_maintenance": ("benchmarks/SinglePrefix/FAT{0}", "maintenance{0}"),
    "ex_uscarrier": ("examples/uscarrier", "USCarrier"),
    "ex_roedunet": ("examples/roedunet", "RoEduNet"),
    "sp_rand": ("examples/generic-algebras", "distance-single"),
}


def get_sp_benchmarks(fmtstr):
    """
    Return the list of input SinglePrefix benchmark files with their destinations.
    Applies to SinglePrefix fatXPol, fatXMaintenance and spX benchmarks.
    """
    common = [(4, 10), (8, 12), (10, 13), (12, 64), (16, 0), (20, 0)]
    benches = [(fmtstr.format(sz), d) for (sz, d) in common]
    return benches


def get_rand_n_p(start: int, stop: int):
    return [(2 ** k, 2 ** -k) for k in range(start, stop)]


def gen_maintenance_benchmarks(benchmarks):
    nvgenpath = os.path.join(os.getcwd(), "nvgen")
    if not os.path.exists(nvgenpath):
        print("Did not find 'nvgen' executable in the current working directory")
        sys.exit(1)
    outputs = []
    for (inputf, dest) in benchmarks:
        hd, tl = os.path.split(inputf)
        # generate the new maintenance version of the fatXPol benchmark
        outputf = os.path.join(hd, tl.replace("sp", "maintenance"))
        args = [nvgenpath, "-d", str(dest), "-o", outputf, inputf, "maintenance"]
        try:
            proc = subprocess.run(args, check=True, capture_output=True)
            print(proc.stdout)
            outputs.append((outputf, dest))
        except subprocess.CalledProcessError as exn:
            print(exn)
            continue
    return outputs


def gen_rand_benchmarks(basefile, benchmarks: list[tuple[int, float]]):
    nvgenpath = os.path.join(os.getcwd(), "nvgen")
    if not os.path.exists(nvgenpath):
        print("Did not find 'nvgen' executable in the current working directory")
        sys.exit(1)
    outputs = []
    for (n, p) in benchmarks:
        topology = f"rand_{n}_{p}"
        outputf = os.path.join("benchmarks/SinglePrefix/Random", topology + ".nv")
        args = [
            nvgenpath,
            "-d",
            "0",
            "-t",
            topology,
            "-o",
            outputf,
            basefile,
            "topology",
        ]
        try:
            proc = subprocess.run(args, check=True, capture_output=True)
            print(proc.stdout)
            outputs.append((outputf, 0))
        except subprocess.CalledProcessError as exn:
            print(exn)
            continue
    return outputs


def simulate_benchmarks(benchmarks):
    """
    Simulate the given benchmarks and collect the results of simulation.
    """
    all_solutions = dict()
    for (inputf, _) in benchmarks:
        solutions = run_nv_simulate(inputf)
        all_solutions[inputf] = solutions
    return all_solutions


def create_benchmarks(benchmarks, cuts, simulate, groups):
    """
    Generate the necessary benchmarks to use.
    """
    for (inputf, dest) in benchmarks:
        for cut in cuts:
            gen_part_nv(
                nvfile=inputf,
                dest=dest,
                cut=FattreeCut.from_str(cut),
                simulate=simulate,
                groups=groups,
            )


def clean_benchmarks(cuts, dry_run):
    """Remove old benchmarks."""
    # pat = re.compile(r"^sp\d*-(part|vpart|pods)\d*\.nv$", re.M)
    cutpat = "|".join(cuts)
    pat = re.compile(r"^(fat\d*Pol|sp\d*)-(" + cutpat + r")(-x)?\d*\.nv$", re.M)
    if dry_run:
        print("clean will remove:")
    # FIXME: take an argument
    for root, _, files in os.walk("benchmarks/"):
        for fname in files:
            if pat.search(fname):
                bench_path = os.path.join(root, fname)
                if dry_run:
                    print(bench_path)
                else:
                    os.remove(bench_path)


def save_results(runs):
    """Save runs to CSV."""
    timestamp = datetime.now()
    time = timestamp.strftime("%Y-%m-%d-%H:%M:%S")
    write_csv(runs, f"kirigami-results-{time}.csv")


def tabulate_fattree_benchmarks(
    directory,
    benchstr,
    sizes,
    cuts,
    z3timeout=3600,
    timeout=3600,
    trials=10,
    parallel=False,
    simulate=True,
    verbose=False,
    log=sys.stdout,
):
    """
    Run all the vertical and horizontal benchmarks.
    directory should be the containing directory for all the benchmarks for the given
    cuts.
    benchstr should be the base name of the NV file, excluding the extension, with a
    str.format position for the size.
    The unpartitioned file should have the format "{benchstr.format(size)}.nv".
    The partitioned files should have the format "{benchstr.format(size)}-{cut}.nv" if
    unsimulated or "{benchstr.format(size)}-{cut}-x.nv" if simulated.
    """
    runs = {}
    if log is not sys.stdout:
        out = open(log, "a")
    else:
        out = sys.stdout
    for size in sizes:
        sim = "-x" if simulate else ""  # for the simulation benchmarks
        benches = [(None, f"{benchstr.format(size)}.nv")] + [
            (cut, f"{benchstr.format(size)}-{cut}{sim}.nv") for cut in cuts
        ]
        if parallel:
            fn = run_trials_parallel
        else:
            fn = run_trials_sync
        try:
            results = fn(
                directory.format(size),
                benches,
                z3timeout,
                timeout,
                trials,
                verbose,
                out,
            )
            runs[directory.format(size)] = results
        except KeyboardInterrupt:
            print("User interrupted benchmarking. Saving partial results...")
            out.close()
            save_results(runs)
    out.close()
    return runs


def main():
    parser = argparse.ArgumentParser(
        description="Frontend for benchmarking the Kirigami tool."
    )
    subparsers = parser.add_subparsers(dest="op")
    hmetis_cuts = [f"hmetis{i + 1}" for i in range(20)]
    cuts = FattreeCut.as_list()

    parser_make = subparsers.add_parser("make")
    parser_make.add_argument(
        "-s",
        "--simulate",
        action="store_true",
        help="generate interface by simulating the given benchmark",
    )
    cut_group = parser_make.add_mutually_exclusive_group()
    cut_group.add_argument(
        "-c",
        "--cuts",
        nargs="+",
        choices=cuts,
        default=["h", "v", "p", "f"],
        help="types of cut across the network (default: %(default)s)",
    )
    cut_group.add_argument(
        "-k",
        "--hmetis",
        nargs="+",
        type=int,
        help="types of hmetis cuts across the network",
    )
    parser_make.add_argument(
        "-b",
        "--benchmark",
        choices=BENCHMARKS.keys(),
        help="which benchmarks to make",
    )
    parser_make.add_argument(
        "-m",
        "--maintenance",
        action="store_true",
        help="generate maintenance version of benchmark first to use",
    )
    parser_make.add_argument(
        "-r",
        "--rand",
        action="store_true",
        help="generate random benchmarks to use first",
    )
    parser_make.add_argument(
        "-ng",
        "--nogroups",
        action="store_false",
        help="don't search for nodes being grouped by any category",
    )

    parser_run = subparsers.add_parser("run")
    parser_run.add_argument(
        "-s", "--sizes", required=True, type=int, nargs="*", help="fattree network size"
    )
    parser_run.add_argument(
        "-p",
        "--parallel",
        action="store_true",
        help="run the benchmarks in parallel using multiprocessing.Pool",
    )
    parser_run.add_argument(
        "-n",
        "--trials",
        type=int,
        help="number of trials to run (default: %(default)s)",
        default=10,
    )
    parser_run.add_argument(
        "-z",
        "--z3time",
        type=int,
        help="number of seconds to run each trial for in z3 (default: %(default)s)",
        default=3600,
    )
    parser_run.add_argument(
        "-t",
        "--timeout",
        type=int,
        help="number of seconds to run each trial for (default: %(default)s)",
        default=3600,
    )
    cut_group = parser_run.add_mutually_exclusive_group()
    cut_group.add_argument(
        "-c",
        "--cuts",
        nargs="+",
        choices=cuts,
        default=["h", "v", "p", "f"],
        help="types of cut across the network (default: %(default)s)",
    )
    cut_group.add_argument(
        "-k",
        "--hmetis",
        nargs="+",
        type=int,
        help="types of hmetis cuts across the network",
    )
    parser_run.add_argument(
        "-b",
        "--benchmark",
        choices=BENCHMARKS.keys(),
        help="which benchmarks to run",
    )
    parser_run.add_argument(
        "-v",
        "--verbose",
        action="store_true",
        help="print the trial's stdout",
    )
    parser_run.add_argument(
        "-l",
        "--log-file",
        nargs="?",
        type=argparse.FileType("w"),
        const=sys.stdout,
        default=sys.stdout,
        help="write output to a given log file",
    )

    parser_clean = subparsers.add_parser("clean")
    parser_clean.add_argument(
        "-d",
        dest="dry_run",
        action="store_true",
        help="print benchmarks without deleting anything",
    )
    cut_group = parser_clean.add_mutually_exclusive_group()
    cut_group.add_argument(
        "-c",
        "--cuts",
        nargs="+",
        choices=cuts,
        default=["h", "v", "p", "f"],
        help="types of cut across the network (default: %(default)s)",
    )
    cut_group.add_argument(
        "-k",
        "--hmetis",
        nargs="+",
        type=int,
        help="types of hmetis cuts across the network",
    )

    args = parser.parse_args()
    directory, benchstr = BENCHMARKS[args.benchmark]
    if args.hmetis:
        chosen_cuts = [f"hmetis{i}" for i in args.hmetis]
    else:
        chosen_cuts = args.cuts
    if args.op == "make":
        fmtstr = os.path.join(directory, benchstr + ".nv")
        benchmarks = get_sp_benchmarks(fmtstr)
        # make intermediate maintenance benchmarks
        if args.maintenance:
            benchmarks = gen_maintenance_benchmarks(benchmarks)
        elif args.rand:
            n_p = get_rand_n_p(4, 12)
            benchmarks = gen_rand_benchmarks(benchmarks[0][0], n_p)
        create_benchmarks(
            benchmarks, chosen_cuts, simulate=args.simulate, groups=args.nogroups
        )
    if args.op == "clean":
        # TODO: change to use benchmark group specified
        clean_benchmarks(chosen_cuts, dry_run=args.dry_run)
    if args.op == "run":
        results = tabulate_fattree_benchmarks(
            directory,
            benchstr,
            args.sizes,
            chosen_cuts,
            z3timeout=args.z3time,
            timeout=args.timeout,
            trials=args.trials,
            parallel=args.parallel,
            verbose=args.verbose,
            log=args.log_file,
        )
        save_results(results)


if __name__ == "__main__":
    main()
