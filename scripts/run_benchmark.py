#!/usr/bin/env python3
"""
Commandline helper to run nv's SMT tool on various benchmarks.
Accepts a benchmark.txt file which can specify benchmarks to run,
where each line of the file has the form:
    [directory] [monolithic benchmark] [cut name:cut benchmarks]*
Each benchmark's result is then saved to a benchmark_output.txt file.
"""
import argparse
from enum import Enum
import multiprocessing
import subprocess
import os
from typing import Optional

# the default name of the NV executable
# we use nv.opt, which is the version with optimizations
NV_CMD = "nv.opt"


# the result of running nv -smt
class RunSmtResult(Enum):
    SUCCEEDED = 0
    TIMEOUT = 1
    ERROR = 2

    def __str__(self):
        match self:
            case RunSmtResult.SUCCEEDED:
                return "Success"
            case RunSmtResult.TIMEOUT:
                return "Timeout"
            case RunSmtResult.ERROR:
                return "Error"


def run_nv_smt(
    nv_exe_path: str,
    benchmark_path: str,
    cut: Optional[str],
    z3time: int,
    time: float,
    cores: int,
) -> tuple[RunSmtResult, str]:
    """
    Run nv's SMT tool and return the result and its output.
    The nv executable is specified by nv_exe_path, and the benchmark to run
    is specified by benchmark_path.
    If it doesn't finish within the given time, kill it.
    """
    if not os.path.exists(nv_exe_path):
        raise Exception(f"Did not find '{nv_exe_path}' executable!")
    # set verbose, SMT flags, and partitioning if needed
    args = [nv_exe_path, "-v", "-m", "-t", str(z3time)]
    if cut is not None:
        # run on multiple cores
        if cores > 1:
            args += ["-p", str(cores)]
        args += ["-k", benchmark_path]
    else:
        args += [benchmark_path]
    output = f"Running {' '.join(args)}\n"
    try:
        proc = subprocess.run(
            args,
            text=True,
            check=True,
            capture_output=True,
            timeout=time,
            encoding="utf-8",
        )
        return RunSmtResult.SUCCEEDED, output + proc.stdout
    except subprocess.CalledProcessError as exn:
        return RunSmtResult.ERROR, "Error: {exn}"
    except subprocess.TimeoutExpired as exn:
        partial_output = exn.output.decode("utf-8")
        return (
            RunSmtResult.TIMEOUT,
            partial_output + f"Timed out (external) at {exn.timeout}",
        )


def run_benchmarks(
    nv_exe_path, benchdir, benches: list[tuple], z3time, time, cores, results_dir
) -> dict[str, str]:
    """
    Run the given benchmarks in the given directory in sequence (once each).
    Return a log of output and a dictionary with the benchmark results for each cut.
    """

    benchmark_outputs = {}
    for (cut, benchmark) in benches:
        result, output = run_nv_smt(
            nv_exe_path, os.path.join(benchdir, benchmark), cut, z3time, time, cores
        )
        if cut is None:
            cut = "monolithic"
        benchmark_outputs[cut] = output
    return benchmark_outputs


def log_nv_smt_run(
    nv_exe_path: str,
    benchmark_path: str,
    cut: Optional[str],
    z3time: int,
    time: float,
    cores: int,
    log_file: str,
):
    result, output = run_nv_smt(nv_exe_path, benchmark_path, cut, z3time, time, cores)
    with open(log_file, "w") as log:
        log.write(f"RESULT: {result}\n")
        log.write(output)


def run_benchmarks_parallel(
    nv_exe_path,
    benchdir,
    benches: list[tuple[str | None, str]],
    z3time: float,
    time: float,
    trials: int,
    cores: int,
    results_dir: str,
):
    """
    Run the given benchmarks in the given directory in parallel, spawning a separate process for each benchmark.
    Log each benchmark's result to a file in results_dir.
    """
    benchmark_args = [
        (
            nv_exe_path,
            os.path.join(benchdir, benchmark),
            cut,
            z3time,
            time,
            cores,
            os.path.join(results_dir, f"{benchmark}-{trial_idx}.txt"),
        )
        for (cut, benchmark) in benches
        for trial_idx in range(trials)
    ]
    with multiprocessing.Pool(processes=trials * len(benches)) as pool:
        pool.starmap(log_nv_smt_run, benchmark_args)


def run_trials_sync(
    nv_exe_path,
    benchdir,
    benches: list[tuple],
    z3time: float,
    time: float,
    trials: int,
    cores: int,
    results_dir: str,
) -> dict[int, dict[str, str]]:
    """
    Run trials of the given benchmarks and return a dictionary of profiling information.
    """
    return {
        i: run_benchmarks(
            nv_exe_path, benchdir, benches, z3time, time, cores, results_dir
        )
        for i in range(trials)
    }


def run_trials_parallel(
    nv_exe_path,
    benchdir,
    benches,
    z3time: float,
    time: float,
    trials: int,
    cores: int,
    results_dir: str,
) -> dict[int, dict[str, str]]:
    """
    Run the benchmarks in the given directory and return a dictionary of
    profiling information.
    Runs each trial in parallel.
    """
    with multiprocessing.Pool(processes=trials) as pool:
        args = [
            (nv_exe_path, benchdir, benches, z3time, time, cores, results_dir)
            for _ in range(trials)
        ]
        runs = pool.starmap(run_benchmarks, args)
        return dict(enumerate(runs))


def run_benchmark_txt(
    nv_exe_path: str,
    txtpath: str,
    results_dir_name: str,
    z3time: float,
    timeout: float,
    trials: int,
    cores: int,
) -> dict[str, dict[int, dict[str, str]]]:
    """
    Run a benchmark.txt file.
    Each line of the file has the following format:
    [directory] [monolithic benchmark] [cut name:cut benchmarks]*
    Filenames must not have spaces!
    Files can contain line comments beginning with a '#'.
    Return a dict from benchmarks to dicts from trials to dicts from cuts to outputs
    (triply-nested dict).
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
                results_dir = os.path.join(directory, results_dir_name)
                # create the results directory if it is missing
                if not os.path.exists(results_dir):
                    os.mkdir(results_dir)
                results = run_benchmarks_parallel(
                    nv_exe_path,
                    directory,
                    benches,
                    z3time=z3time,
                    time=timeout,
                    trials=trials,
                    cores=cores,
                    results_dir=results_dir,
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
        "-x",
        "--nv-path",
        default=os.path.join(os.getcwd(), NV_CMD),
        help="which executable to run as NV (default: %(default))",
    )
    parser.add_argument(
        "-d",
        "--results-dir",
        default="results",
        help="name of the directory to store results (default: %(default)) inside the benchmarks' directory",
    )
    parser.add_argument(
        "-n",
        "--trials",
        type=int,
        help="number of trials to run (default: %(default)s)",
        default=1,
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
        "-p",
        "--parallel",
        type=int,
        help="number of cores to use for each trial (default: %(default)s)",
        default=1,
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
        args.nv_path,
        args.file,
        args.results_dir,
        args.z3time,
        args.timeout,
        args.trials,
        args.parallel,
    )
    # if verbose, print the output to stdout
    # if args.verbose:
    #     for (b, trials) in runs.items():
    #         for (t, cuts) in trials.items():
    #             for (c, output) in cuts.items():
    #                 print(f"Benchmark {b}, trial {t}, cut {c}:")
    #                 print(output)
