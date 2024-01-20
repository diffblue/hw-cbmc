import psutil
import torch

from tracing.trace_handle import Trace
from termination import tracing, cegs_tracing



processes = psutil.cpu_count(logical=False)




def get_and_layout_traces(vcds, limit, tracing_seed, res):

    trace = Trace(vcds)

    input_vars = trace.get_pos_identifiers(frame=5)
    input_dim = len(input_vars)

    input_before = []
    input_after = []

    # creating data and model with info from trace
    try:
        head_input_before, head_input_after = trace.pair_all_traces_multi_as_tensor() # TODO CHANGE THIS
    except RuntimeError as e:
        res['error'] = str(e)
        return res
    input_before.append(head_input_before)
    input_after.append(head_input_after)

    return input_vars, input_before, input_after


def add_new_traces(zero_input_before, zero_input_after, jarfile, classname, methodname, samples, limit, loop_heads, tracing_seed, res, cegs_file):

    res['tracing'], trace = cegs_tracing(jarfile, classname, methodname,
                                    samples, limit, loop_heads,
                                    tracing_seed, cegs_file,
                                    num_processes=processes)

    input_vars = trace.get_pos_identifiers(frame=5)
    input_dim = len(input_vars)

    input_before = []
    input_after = []

    # creating data and model with info from trace

    for index,head in enumerate(loop_heads):
        try:
            head_input_before, head_input_after = trace.pair_all_traces_multi_as_tensor(head,
                                                                                        loop_heads)  # TODO CHANGE THIS
        except RuntimeError as e:
            res['error'] = str(e)
            return res

        input_before.append(torch.cat((zero_input_before[index], head_input_before)))
        input_after.append(torch.cat((zero_input_after[index], head_input_after)))

    return input_vars, input_before, input_after


def get_and_layout_traces_mvgaussian(jarfile, classname, methodname, samples, limit, loop_heads, tracing_seed, res):
    res['tracing'], trace = tracing(jarfile, classname, methodname,
                                    samples, limit, loop_heads,
                                    tracing_seed, sampling_strategy='gaussian',
                                    num_processes=processes)

    input_vars = trace.get_pos_identifiers(frame=5)
    input_dim = len(input_vars)

    input_before = []
    input_after = []

    # creating data and model with info from trace

    for head in loop_heads:
        try:
            head_input_before, head_input_after = trace.pair_all_traces_multi_as_tensor(head,
                                                                                        loop_heads)  # TODO CHANGE THIS
        except RuntimeError as e:
            res['error'] = str(e)
            return res
        input_before.append(head_input_before)
        input_after.append(head_input_after)

    return (input_vars, input_before, input_after)

