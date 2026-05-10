import os
import subprocess
from typing import List
from typing import Tuple
import torch
import pathlib
import tempfile
import json
import time

#TODO Use path.join
AGENT_LD_PATH = str(pathlib.Path(__file__).parent.absolute()) + '/../../libs'
GEN_AND_TRACE_JAR =  str(pathlib.Path(__file__).parent.absolute()) + '/../../libs/GenAndTrace.jar'


def pairing(ls: List) -> Tuple[List, List]:
    if ls == []:
        return [], []
    before, after = [], []
    for i in range(len(ls) - 1):
        before += [ls[i]]
        after += [ls[i + 1]]
    return before, after


def chunks(l, n):
    n = max(1, n)
    return (l[i:i + n] for i in range(0, len(l), n))


def create_run_command(input_program, class_name, method_name, output_file, sampling_strategy, samples, loopheads=None,
                       seed=None, tracelimit=None, cegs_file=None):

    environment = dict(os.environ)

    cmd = 'java'
    if 'JAVA_HOME' in os.environ:
        cmd = '{}/bin/java'.format(environment['JAVA_HOME'])

    jvmti_agent_cmd = None

    if loopheads is None:
        jvmti_agent_cmd = '-agentlib:JavaMemTraceAgent=class={},method={},output={}' \
            .format(class_name, method_name, output_file)
    else:
        jvmti_agent_cmd = '-agentlib:JavaMemTraceAgent=class={},method={},output={},loopheads={}' \
            .format(class_name, method_name, output_file, ':'.join(map(str, loopheads)))

    if tracelimit is not None:
        jvmti_agent_cmd = "{},tracelimit={}".format(jvmti_agent_cmd, tracelimit)


    if cegs_file is None:
        command = [cmd, jvmti_agent_cmd,
                   '-jar', GEN_AND_TRACE_JAR,
                   '-j', input_program,
                   '-c', class_name,
                   '-m', method_name,
                   '-strategy', sampling_strategy]
    else:
        command = [cmd, jvmti_agent_cmd,
                   '-jar', GEN_AND_TRACE_JAR,
                   '-j', input_program,
                   '-c', class_name,
                   '-m', method_name,
                   '-cegs', cegs_file]

    print(command)
    # assert seed is not None
    if seed is not None:
        command = command + ['-seed', str(seed)]

    command = command + ['-s', str(samples)]


    return command


def run_tracing(input_program, class_name, method_name, output_file, samples, loopheads=None, tracelimit=None,
                seed=None, sampling_strategy="default", num_processes=1):

    if num_processes < 1:
        num_processes = 1
    if samples < num_processes:
        num_processes = 1

    environment = dict(os.environ)
    environment['LD_LIBRARY_PATH'] = AGENT_LD_PATH


    # ##### multiprocessing
    # number of samples might not be exactly the number of requested samples due to rounding
    samples_per_process = samples // num_processes
    print("Creating {} samples on {} processes. Requested sample size {} actual sample size {}"
          .format(samples_per_process, num_processes, samples_per_process * num_processes, samples))

    #assert seed is not None
    processes = []
    for i in range(0, num_processes):
        f = tempfile.NamedTemporaryFile()

        run_cmd = create_run_command(input_program, class_name, method_name, f.name, sampling_strategy,
                                     samples_per_process, loopheads=loopheads, seed=seed, tracelimit=tracelimit)

        p = subprocess.Popen(run_cmd, env=environment, stdout=subprocess.PIPE)
        processes.append((f, p))

    print("Running traces with {} processes with {} samples each.".format(num_processes, samples_per_process))

    start = time.time()

    json_object = None
    for f, p in processes:
        p.wait()
        if json_object is None:
            json_object = json.load(f)
        else:
            json_object["traces"] += json.load(f)["traces"]
            f.close()

    if json_object is None:
        raise Exception("Json Object is None, something went wrong")
    else:
        with open(output_file, 'w') as f:
            json.dump(json_object, f, indent=4)

    tracing_time = time.time() - start

    print("Tracing and processing results finished in {}.".format(tracing_time))

    # subprocess.run(command,env=environment)


def run_cegs_tracing(input_program, class_name, method_name, output_file, samples, cegs_file, loopheads=None, tracelimit=None,
                seed=None, num_processes=1):

    if num_processes < 1:
        num_processes = 1
    if samples < num_processes:
        num_processes = 1

    environment = dict(os.environ)
    environment['LD_LIBRARY_PATH'] = AGENT_LD_PATH

    print("LH:   {}".format(loopheads))
    print("CEGS: {}".format(cegs_file))


    # ##### multiprocessing
    # number of samples might not be exactly the number of requested samples due to rounding
    samples_per_process = samples // num_processes
    print("Creating {} samples on {} processes. Requested sample size {} actual sample size {}"
          .format(samples_per_process, num_processes, samples_per_process * num_processes, samples))
    #assert seed is not None
    processes = []
    for i in range(0, num_processes):
        f = tempfile.NamedTemporaryFile(delete=True)
        run_cmd = create_run_command(input_program, class_name, method_name, f.name, "pairanticorr",
                                     samples_per_process, loopheads=loopheads, seed=seed, tracelimit=tracelimit, cegs_file=cegs_file)

        print(" ".join(map(str, run_cmd)))

        p = subprocess.Popen(run_cmd, env=environment, stdout=subprocess.PIPE)

        processes.append((f, p))

    print("Running traces with {} processes with {} samples each.".format(num_processes, samples_per_process))

    start = time.time()

    json_object = None
    for f, p in processes:
        p.wait()

        if json_object is None:
            json_object = json.load(f)
        else:
            json_object["traces"] += json.load(f)["traces"]

        f.close()


    if json_object is None:
        raise Exception("Json Object is None, something went wrong")
    else:
        with open(output_file, 'w') as f:
            json.dump(json_object, f, indent=4)

    tracing_time = time.time() - start

    print("Tracing and processing results finished in {}.".format(tracing_time))

    # subprocess.run(command,env=environment)
