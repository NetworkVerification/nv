#!/usr/bin/python3
"""
Compute benchmark results comparing partitioned and unpartitioned SMT checks.
Takes output of runs of NV as input and produces a CSV.
"""
import re
from datetime import datetime
import sys
import csv
from typing import Any, Union


def parse_smt(output: str) -> dict[str, list[Union[int, float]]]:
    """
    Parse the output of an NV command.
    Return a dictionary of operations to lists of times taken by those operations.
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


def write_csv(rows: list[dict[str, Any]], path: str):
    """
    Write the results dictionary to a CSV.
    Each line of the CSV describes an operation run for a given cut during a given trial,
    some number of times (some operations may run many times if the cut produces many subnetworks).
    """
    fields = rows[0].keys()
    with open(path, "w") as csvf:
        writer = csv.DictWriter(csvf, fieldnames=list(fields), restval="")
        writer.writeheader()
        for row in rows:
            writer.writerow(row)


def save_results(runs: list[dict[str, Any]], prefix="kirigami-results"):
    """Save runs to CSV."""
    timestamp = datetime.now()
    time = timestamp.strftime("%Y-%m-%d-%H:%M:%S")
    write_csv(runs, f"{prefix}-{time}.csv")


def parse_file_name(file_name: str) -> tuple:
    """
    Return the benchmark group, cut and trial that a file represents.
    Assumes the file name has the form "{prefix}[-cut].nv-{cut}-{trial}.txt".
    """
    pat = re.compile(r"([\w_\.]*)(?:-.*)?\.nv-(\w*)-([0-9]*)\.txt")
    m = pat.search(file_name)
    if m is not None:
        return m.groups()
    else:
        raise ValueError(f"Unable to parse file name {file_name}")


def collect_results(
    files: list[str],
) -> dict[str, dict[str, dict[int, dict[int, dict[str, Union[int, float]]]]]]:
    """
    Collect the results of the SMT output for each provided file.
    Each file is treated as a separate benchmark column.
    """
    results = {}

    for f in files:
        with open(f, "r") as data:
            bench, cut, trial = parse_file_name(f)
            operation_times = parse_smt(data.read())
            for (operation, times) in operation_times.items():
                if operation not in results:
                    results[operation] = {}
                if cut not in results[operation]:
                    results[operation][cut] = {}
                if trial not in results[operation][cut]:
                    results[operation][cut][trial] = {}
                for (i, time) in enumerate(times):
                    if i not in results[operation][cut][trial]:
                        results[operation][cut][trial][i] = {}
                    results[operation][cut][trial][i][bench] = time
    return results


if __name__ == "__main__":
    # each file passed in is treated as a column
    # first we build a nested series of dictionaries storing the times
    results = collect_results(sys.argv[1:])
    # then we write these out as CSV rows
    rows = [
        ({"operation": operation, "cut": cut, "trial": trial, "occurrence": i} | times)
        for (operation, cuts) in results.items()
        for (cut, trials) in cuts.items()
        for (trial, occurrences) in trials.items()
        for (i, times) in occurrences.items()
    ]
    save_results(rows)
