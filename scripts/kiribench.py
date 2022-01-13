#!/usr/bin/env python3
"""
Main module to generate, run and tabulate the Kirigami benchmarks.
"""

import argparse
import os
import re
import sys
from gen_part_nv import gen_part_nv, run_nv_simulate, FattreeCut
from tabulator import (
    run_trials_sync,
    run_trials_parallel,
    save_results,
)

SP_FAT_BENCHMARKS = {
    "sp": ("benchmarks/SinglePrefix/FAT{size}/", "sp{size}"),
    "sp_fatpol": ("benchmarks/SinglePrefix/FAT{size}", "fat{size}Pol"),
    "sp_maintenance": ("benchmarks/SinglePrefix/FAT{size}", "maintenance{size}"),
}

TOPZOO_BENCHMARKS = {
    "ex_uscarrier": ("examples/TopologyZoo/uscarrier", "USCarrier"),
    "ex_roedunet": ("examples/TopologyZoo/roedunet", "RoEduNet"),
    "ex_kdl": ("examples/TopologyZoo/kdl", "kdl"),
}

RAND_BENCHMARKS = {
    "sp_rand": ("benchmarks/SinglePrefix/Random", "sp_{n}_{p}"),
}


def get_sp_fat_benchmarks(fmtstr: str) -> list[tuple[str, int]]:
    """
    Return the list of input SinglePrefix benchmark files with their destinations.
    Applies to SinglePrefix fatXPol, fatXMaintenance and spX benchmarks.
    """
    common = [(4, 10), (8, 12), (10, 13), (12, 64), (16, 0), (20, 0)]
    benches = [(fmtstr.format(size=sz), d) for (sz, d) in common]
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
    Run all the benchmarks.
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
                directory.format(size=size),
                benches,
                z3timeout,
                timeout,
                trials,
                verbose,
                out,
            )
            runs[directory.format(size=size)] = results
        except KeyboardInterrupt:
            print("User interrupted benchmarking. Saving partial results...")
            out.close()
            save_results(runs)
    out.close()
    return runs


def parse_cuts(parser: argparse.ArgumentParser):
    """Add a parse group for cuts to the given parser."""
    cut_group = parser.add_mutually_exclusive_group()
    cut_group.add_argument(
        "-c",
        "--cuts",
        nargs="+",
        choices=FattreeCut.as_list(),
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
    parse_cuts(parser_make)
    parser_make.add_argument(
        "-b",
        "--benchmark",
        choices=SP_FAT_BENCHMARKS.keys(),
        help="which benchmarks to make",
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
    parse_cuts(parser_run)
    parser_run.add_argument(
        "-b",
        "--benchmark",
        choices=SP_FAT_BENCHMARKS.keys(),
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
    parse_cuts(parser_clean)

    args = parser.parse_args()
    directory, benchstr = SP_FAT_BENCHMARKS[args.benchmark]
    if args.hmetis:
        chosen_cuts = [f"hmetis{i}" for i in args.hmetis]
    else:
        chosen_cuts = args.cuts
    if args.op == "make":
        fmtstr = os.path.join(directory, benchstr + ".nv")
        benchmarks = get_sp_fat_benchmarks(fmtstr)
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
