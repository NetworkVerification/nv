#!/usr/bin/python3
"""
Compute benchmark results comparing partitioned and unpartitioned SMT checks.
"""
import argparse
from datetime import datetime
import multiprocessing
import subprocess
import os
import sys
import re
import csv
from typing import Any, Optional


def join_cut_dicts(
    *dicts: tuple[str, Optional[str], dict[str, Any]]
) -> tuple[str, dict[str, dict[str, Any]]]:
    """
    Join the results dictionaries for separate cuts into a single dictionary over all cuts.
    """
    joined = dict()
    logs = ""
    for (log, cut, results) in dicts:
        if cut is None:
            cut = "monolithic"
        joined[cut] = results
        logs += log
    return logs, joined


def parse_smt(output: str) -> dict[str, list[int | float]]:
    """
    Parse the output of an NV command.
    Returns a dictionary of strings to lists of floats.
    """
    action = re.compile(r"(.*) took: (\d*\.?\d+) secs to complete", re.M)
    z3action = re.compile(r"^\s*:(\w*)\s*(\d*\.?\d+)", re.M)
    assertion = re.compile(r"Assertion (\d*) failed", re.M)
    guarantee = re.compile(r"Guarantee (\d*) failed", re.M)
    z3timeout = re.compile(r"Z3 timed out after (\d*)", re.M)
    profile = dict()
    # get transformation profiling
    for match in action.finditer(output):
        transform = match.group(1)
        time = float(match.group(2))
        profile.setdefault(transform, list()).append(time)
    # get z3 profiling
    for match in z3action.finditer(output):
        stat = "z3 " + match.group(1)
        qua = float(match.group(2))
        profile.setdefault(stat, list()).append(qua)
    # get assertion failures
    for match in assertion.finditer(output):
        assn = int(match.group(1))
        profile.setdefault("failed asserts", list()).append(assn)
    # get guarantee failures
    for match in guarantee.finditer(output):
        guar = int(match.group(1))
        profile.setdefault("failed guars", list()).append(guar)
    # get z3 timeouts
    for match in z3timeout.finditer(output):
        time = int(match.group(1))
        profile.setdefault("z3 timeout", list()).append(time)
    return profile


def run_nv_smt(path: str, cut: Optional[str], z3time: int, time: float, verbose: bool):
    """
    Run nv's SMT tool and capture its output.
    If it doesn't finish within the given time, kill it.
    """
    log = ""
    nvcmd = "nv.opt"
    nvpath = os.path.join(os.getcwd(), nvcmd)
    if not os.path.exists(nvpath):
        raise Exception(
            f"Did not find '{nvcmd}' executable in the current working directory!"
        )
    # set verbose, SMT flags, and partitioning if needed
    args = [nvpath, "-v", "-m", "-t", str(z3time)]
    if cut is not None:
        args += ["-k", path]
    else:
        args += [path]
    log += f"Running {' '.join(args)}\n"
    try:
        proc = subprocess.run(
            args,
            text=True,
            check=True,
            capture_output=True,
            timeout=time,
            encoding="utf-8",
        )
        if verbose:
            log += proc.stdout + "\n"
        return log, parse_smt(proc.stdout)
    except subprocess.CalledProcessError as exn:
        if verbose:
            log += exn.output.decode("utf-8") + "\n"
        log += f"Error: {exn}\n"
        return log, {}
    except subprocess.TimeoutExpired as exn:
        partial_output = exn.output.decode("utf-8")
        if verbose:
            log += partial_output + "\n"
        log += f"Timeout (external) after {exn.timeout} seconds: {exn}\n"
        parsed = parse_smt(partial_output)
        parsed["external timeout"] = [exn.timeout]
        return log, parsed


def run_bench(cut, path, z3time, time, verbose):
    log, result = run_nv_smt(path, cut, z3time, time, verbose)
    return (log, cut, result)


def run_benchmarks_sync(benchdir, benches, z3time, time, verbose) -> tuple[str, dict]:
    """
    Run the given benchmarks in the given directory in sequence (once each).
    Return a log of output and a dictionary with the benchmark results for each cut.
    """
    return join_cut_dicts(
        *[
            run_bench(c, os.path.join(benchdir, n), z3time, time, verbose)
            for (c, n) in benches
        ]
    )


def run_trials_sync(benchdir, benches, z3time, time, trials, verbose, logfile):
    """
    Run trials of the given benchmarks and return a dictionary of profiling information.
    """
    runs = {}
    for i in range(trials):
        logfile.write("Running trial " + str(i + 1) + " of " + str(trials) + "\n")
        logs, results = run_benchmarks_sync(benchdir, benches, z3time, time, verbose)
        logfile.write(logs)
        runs[i] = results
    return runs


def run_trials_parallel(benchdir, benches, z3time, time, trials, verbose, logfile):
    """
    Run the benchmarks in the given directory and return a dictionary of
    profiling information.
    Runs each trial in parallel.
    """
    with multiprocessing.Pool(processes=trials) as pool:
        args = [(benchdir, benches, z3time, time, verbose) for _ in range(trials)]
        runs = pool.starmap(run_benchmarks_sync, args)
        logs, results = map(list, zip(*runs))
        results = dict(enumerate(results))
        logfile.write("".join(logs))
        return results


def invert_results_dict(results):
    """
    Flatten the results nested dictionary into a CSV-writable format.
    Results has the following nested structure as input:
    dict[directory, dict[trial, dict[cut, dict[operation, list of occurrences]]]]
    The output instead has the form:
    list[dict[str,str]] of N elements, where each element has the following keys:
    - 'trial'
    - 'cut'
    - 'operation'
    - 'occurrence'
    - and a key for each directory
    and N = #trials * #cuts * #operations * #occurrences
    """
    output: dict[tuple, dict] = {}
    for (benchmark, trials) in results.items():
        for (trial, cuts) in trials.items():
            for (cut, ops) in cuts.items():
                for (op, occurrences) in ops.items():
                    for (i, t) in enumerate(occurrences):
                        common_hash = (trial, cut, op, i)
                        output.setdefault(common_hash, dict())[f"{benchmark}"] = t
    rows = []
    for ((t, c, o, i), data) in output.items():
        common = {"operation": o, "cut": c, "trial": t, "occurrence": i}
        common.update(data)
        rows.append(common)
    return rows


def write_csv(results: dict[str, dict[str, dict]], path):
    """
    Write the results dictionary to a CSV.
    Each line of the CSV describes an operation run for a given cut during a given trial,
    some number of times (some operations may run many times if the cut produces many subnetworks).
    """
    output = invert_results_dict(results)
    fields = output[0].keys()
    with open(path, "w") as csvf:
        writer = csv.DictWriter(csvf, fieldnames=list(fields), restval="")
        writer.writeheader()
        for row in output:
            writer.writerow(row)


def save_results(runs):
    """Save runs to CSV."""
    timestamp = datetime.now()
    time = timestamp.strftime("%Y-%m-%d-%H:%M:%S")
    write_csv(runs, f"kirigami-results-{time}.csv")


def run_benchmark_txt(txtpath: str, z3time, timeout, trials, verbose):
    """
    Run a benchmark.txt file.
    Each line of the file has the following format:
    [directory] [monolithic benchmark] [cut name:cut benchmarks]*
    Filenames must not have spaces!
    Files can contain line comments beginning with a '#'.
    """
    runs = {}
    with open(txtpath, "r") as benchmark_file:
        for benchmarks in benchmark_file.readlines():
            # skip comments
            if benchmarks.startswith("#"):
                continue
            directory, monolithic, *cuts = benchmarks.split()
            benches: list[tuple[Optional[str], str]] = [(None, monolithic)]
            for cut in cuts:
                cut_name, cut_path = cut.split(":")
                benches.append((cut_name, cut_path))
            try:
                results = run_trials_parallel(
                    directory,
                    benches,
                    z3time=z3time,
                    time=timeout,
                    trials=trials,
                    verbose=verbose,
                    logfile=sys.stdout,
                )
                benchmark_key = os.path.join(directory, monolithic)
                runs[benchmark_key] = results
            except KeyboardInterrupt:
                print("User interrupted benchmarking. Exiting with partial results...")
                break
    return runs


def parser():
    parser = argparse.ArgumentParser(
        description="Frontend for running Kirigami benchmarks."
    )
    parser.add_argument(
        "file",
        help="benchmark.txt file describing which benchmarks to run",
    )
    parser.add_argument(
        "-n",
        "--trials",
        type=int,
        help="number of trials to run (default: %(default)s)",
        default=5,
    )
    parser.add_argument(
        "-z",
        "--z3time",
        type=int,
        help="number of seconds to run each trial for in z3 (default: %(default)s)",
        default=3600,
    )
    parser.add_argument(
        "-t",
        "--timeout",
        type=int,
        help="number of seconds to run each trial for (default: %(default)s)",
        default=3600,
    )
    parser.add_argument(
        "-v",
        "--verbose",
        action="store_true",
        help="print the trial's stdout",
    )
    return parser


if __name__ == "__main__":
    args = parser().parse_args()
    runs = run_benchmark_txt(
        args.file, args.z3time, args.timeout, args.trials, args.verbose
    )
    save_results(runs)
