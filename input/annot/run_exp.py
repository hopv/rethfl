#!/usr/bin/env python3

import argparse
import os
import subprocess
import signal
import re
import pandas as pd
from tqdm import tqdm


# Default value is for the short experiment with no repeat
timeout = 30
repeat = 1
bar = None

class BenchInstance:
    name = ""
    annot_files = []
    def __init__(self, name, annot_files):
        self.name = name
        self.annot_files = annot_files

    def create_options(self):
        ret = [[]]
        for f in self.annot_files:
            ret += [["--annot", f, "--target", "annotation"],
                    ["--annot", f, "--target", "toplevel"]
                    ]
        return ret

BENCHMARK = [
    BenchInstance('array_init.hfl', ["array_init.annot"]),
    BenchInstance('kmp.hfl', ["kmp.loop.annot", "kmp.loopShift.annot"]),
    BenchInstance('memoization.hfl', ['memoization.annot']),
    BenchInstance('merge.hfl', ['merge.annot']),
    BenchInstance('soli.hfl', ["soli.annot"]),
    BenchInstance('up3.hfl', ['up3Loopa.annot', 'up3Loopb.annot']),
]


class Config:
    def __init__(self):
        pass

parser = argparse.ArgumentParser()
parser.add_argument("--full", help="Runs the full experiment, which may take some time. Forces timeout = 300 and repeat = 5",  action='store_true')
parser.add_argument("--timeout", help="timeout in seconds (default 60)", default=timeout, type=int)
parser.add_argument("--repeat", help="number of repetition (default 1)", default=repeat, type=int)

args = parser.parse_args()

def run_instance(instance, df):
    for options in instance.create_options():
        for solver in ["hoice", "z3"]:
            cmd = ['rethfl', instance.name] + options + ["--solver", solver]
            stdout, stderr, timed_out = run(cmd)
            stdout = stdout.decode('utf-8')
            total, smt_file = parse_output(stdout, timed_out)
            pvars, chcs =  count_from_smt_file(smt_file)
            option_str = " ".join(options + ["--solver", solver])
            #print(f"SMT file:{smt_file} Pvars:{pvars} CHCs:{chcs} Total:{total}")

            # Add new datas to the dataframe
            row = pd.DataFrame(columns=df.columns, data=[[instance.name, option_str ,total, pvars, chcs]])
            df = pd.concat([df, row], ignore_index=True)

            bar.update(1)
    return df

def parse_output(output, timed_out):
    if timed_out:
        ## If it timed out we set the limit
        total = timeout
    else:
        pattern = r"total:\s(.*)\ssec"
        match = re.search(pattern, output)
        total = float(match.group(1))

    pattern = r"CHC file:\s(.*\.smt2)"
    match = re.search(pattern, output)
    smt_file = match.group(1)

    return total, smt_file

def count_from_smt_file(smt_file):
    with open(smt_file, 'r') as f:
        content = f.read()

        pattern = r'\(assert'
        matches = re.findall(pattern, content)
        chcs = len(matches)

        pattern = r'\(declare-fun'
        matches = re.findall(pattern, content)

        pvars = len(matches)

    return pvars, chcs

def run(cmd):
    cmd = " ".join(cmd)
    proc = subprocess.Popen(cmd, shell=True, stdout=subprocess.PIPE, preexec_fn=os.setsid)
    try:
        stdout, stderr = proc.communicate(timeout=timeout)
        return stdout, stderr, False
    except subprocess.TimeoutExpired:
        os.killpg(os.getpgid(proc.pid), signal.SIGTERM)
        stdout, stderr = proc.communicate()
        return stdout, stderr, True

def main():
    # Set the global variables
    global timeout
    global repeat
    timeout = args.timeout
    repeat = args.repeat

    if args.full:
        timeout = 300
        repeat = 5

    # Set up progress bar
    number_of_runs = 0
    for instance in BENCHMARK:
        # *2 is because we run two backend CHC solvers
        number_of_runs += 2 * len(instance.create_options())
    number_of_runs *= repeat
    global bar
    bar = tqdm(total = number_of_runs)

    df = pd.DataFrame(columns=['FILE', 'OPTION', 'TOTAL', 'PVars', "CHCs"])

    # Main loop
    for _ in range(repeat):
        for instance in BENCHMARK:
            df = run_instance(instance, df)

    bar.close()
    # Calculate the average
    df[df.columns[1]].fillna(' --', inplace=True)
    df = df.groupby([df.columns[0], df.columns[1]])[[df.columns[2], df.columns[3], df.columns[4]]].mean().reset_index()

    # Dump the result
    pd.set_option('display.max_colwidth', None)
    pd.set_option('display.max_rows', None)
    with open('result.txt', 'w' ) as f:
        print(df, file=f)

if __name__ == '__main__':
    main()
