#!/usr/bin/env python3
"""
Main module to generate, run and tabulate the Kirigami benchmarks.
"""

import argparse
import os
import re
from datetime import datetime
from gen_part_nv import gen_part_nv, run_nv_simulate, CUTS
from tabulate_sp_bench import (
    run_trials_sync,
    run_trials_parallel,
    write_csv,
    DISTINCT_OPERATIONS,
)

BENCHMARKS = {
    # Single Prefix
    "sp": ("benchmarks/SinglePrefix/FAT{0}/", "sp{0}"),
    "sp_fatpol": ("benchmarks/SinglePrefix/FAT{0}", "fat{0}Pol"),
    "sp_topzoo": ("benchmarks/SinglePrefix/TopologyZoo", "USCarrier"),
    "ap_fatpol": ("benchmarks/AllPrefixes/FAT{0}", "fat{0}Pol"),
    "ap_topzoo": ("benchmarks/AllPrefixes/TopologyZoo", "USCarrier"),
}


def get_sp_benchmarks(fmtstr):
    """
    Return the list of input SinglePrefix benchmark files with their destinations.
    Applies to SinglePrefix fatXPol and spX benchmarks.
    """
    common = [(4, 10), (8, 12), (10, 13), (12, 64), (16, 0), (20, 0)]
    benches = [(fmtstr.format(sz), d) for (sz, d) in common]
    return benches


def simulate_benchmarks(benchmarks):
    """
    Simulate the given benchmarks and collect the results of simulation.
    """
    all_solutions = dict()
    for (inputf, _) in benchmarks:
        solutions = run_nv_simulate(inputf)
        all_solutions[inputf] = solutions
    return all_solutions


def create_benchmarks(benchmarks, cuts, simulate):
    """
    Generate the necessary benchmarks to use.
    """
    for (inputf, dest) in benchmarks:
        for cut in cuts:
            gen_part_nv(inputf, dest, cut, simulate)


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
    return write_csv(runs, f"kirigami-results-{time}.csv")


def tabulate_fattree_benchmarks(
    directory,
    benchstr,
    sizes,
    cuts,
    timeout=3600,
    trials=10,
    parallel=False,
    simulate=True,
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
    runs = []
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
                directory.format(size), benches, timeout, trials, DISTINCT_OPERATIONS
            )
            runs.append(results)
        except KeyboardInterrupt:
            print("User interrupted benchmarking. Saving partial results...")
            save_results(runs)
    return runs


def main():
    parser = argparse.ArgumentParser(
        description="Frontend for benchmarking the Kirigami tool."
    )
    subparsers = parser.add_subparsers(dest="op")

    parser_make = subparsers.add_parser("make")
    parser_make.add_argument(
        "-s",
        "--simulate",
        action="store_true",
        help="generate interface by simulating the given benchmark",
    )
    parser_make.add_argument(
        "-c",
        "--cuts",
        nargs="+",
        choices=CUTS,
        default=["h", "v", "p"],
        help="types of cut across the network (default: %(default)s)",
    )
    parser_make.add_argument(
        "-b",
        "--benchmark",
        choices=BENCHMARKS.keys(),
        help="which benchmarks to make",
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
        "-t",
        "--timeout",
        type=int,
        help="number of seconds to run each trial for (default: %(default)s)",
        default=3600,
    )
    parser_run.add_argument(
        "-c",
        "--cuts",
        nargs="+",
        choices=CUTS,
        default=["h", "v", "p"],
        help="types of cut across the network (default: %(default)s)",
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

    parser_clean = subparsers.add_parser("clean")
    parser_clean.add_argument(
        "-d",
        dest="dry_run",
        action="store_true",
        help="print benchmarks without deleting anything",
    )
    parser_clean.add_argument(
        "-c",
        "--cuts",
        nargs="+",
        choices=CUTS,
        default=["h", "v", "p"],
        help="types of cut across the network (default: %(default)s)",
    )

    args = parser.parse_args()
    directory, benchstr = BENCHMARKS[args.benchmark]
    if args.op == "make":
        fmtstr = os.path.join(directory, benchstr + ".nv")
        benchmarks = get_sp_benchmarks(fmtstr)
        create_benchmarks(benchmarks, args.cuts, simulate=args.simulate)
    if args.op == "clean":
        # TODO: change to use benchmark group specified
        clean_benchmarks(args.cuts, dry_run=args.dry_run)
    if args.op == "run":
        results = tabulate_fattree_benchmarks(
            directory,
            benchstr,
            args.sizes,
            args.cuts,
            timeout=args.timeout,
            trials=args.trials,
            parallel=args.parallel,
            verbose=args.verbose,
        )
        save_results(results)


if __name__ == "__main__":
    main()
