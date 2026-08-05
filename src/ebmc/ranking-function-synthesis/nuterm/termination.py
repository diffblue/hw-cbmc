from models.SingleLinearWithRelu import SingleLinearWithRelu
from tracing.trace_handle import Trace
from loopheads import get_loop_heads

from models.SingleLinear import SingleLinear

from tracing.utils import *

import torch.optim as optim
from learning import *

from tracing.trace_handle import Trace

from javachecker import *
import time

import numpy as np
from numpy.linalg import norm

def tracing(PROGRAM, CLASS, FUNCTION, SAMPLES, limit, LOOP_OFFSET, tracing_seed, sampling_strategy="default", num_processes=1):
    # ######### TRACING ##########
    print('=' * 40)
    print(' - Tracing')
    print('=' * 40)

    f = tempfile.NamedTemporaryFile()
    print("Traces are being written to {}.".format(f.name))

    #assert tracing_seed is not None
    start = time.time()  # process_time excludes the time taken by the traces

    run_tracing(PROGRAM, CLASS, FUNCTION, f.name, SAMPLES, LOOP_OFFSET, seed=tracing_seed,
                tracelimit=limit, sampling_strategy=sampling_strategy, num_processes=num_processes)
    tracing_time = time.time() - start

    # reading trace
    trace = Trace(f.name)
    # assert trace.number_of_traces() == SAMPLES,'number of traces should be {}'.format(SAMPLES)
        
    return tracing_time, trace


def cegs_tracing(PROGRAM, CLASS, FUNCTION, SAMPLES, limit, LOOP_OFFSET, tracing_seed, cegs_file, num_processes=1):
    # ######### TRACING ##########
    print('=' * 40)
    print(' - CEGS Tracing')
    print('=' * 40)

    TRACE_FILE = 'cegs_test.json'
    # assert tracing_seed is not None
    start = time.time()  # process_time excludes the time taken by the traces
    run_cegs_tracing(PROGRAM, CLASS, FUNCTION, TRACE_FILE, SAMPLES, loopheads=LOOP_OFFSET, cegs_file=cegs_file,seed=tracing_seed,
                tracelimit=limit, num_processes=num_processes)
    tracing_time = time.time() - start

    # reading trace
    trace = Trace(TRACE_FILE)
    # assert trace.number_of_traces() == SAMPLES,'number of traces should be {}'.format(SAMPLES)

    return tracing_time, trace

def run_learning(trace, LOOP_OFFSET, MODEL, learning_function, loss_function):
    # ######### LEARNING ##########
    print('='*40)
    print(' - Learning')
    print('='*40)

    start = time.time()
    model, loss = learning_function(trace, LOOP_OFFSET, Model=MODEL, loss_func=loss_function)
    model.print_sympy()
    learning_time = time.time() - start

    print("loss: ", loss)
    
    return learning_time, model, loss


def run_checking(PROGRAM, CLASS, FUNCTION, LOOP_OFFSET, model):

    # ########## CHECKING ########
    print('=' * 40)
    print(' - Checking')
    print('=' * 40)

    S = model.get_round_scaling()
    start = time.time()
    (decreases, bounded) = check(PROGRAM,
                                 CLASS,
                                 FUNCTION, LOOP_OFFSET,
                                 model.input_vars, 
                                 [int(x*S) for x in model.get_round_weights()[0]] + [0])  # Last 0 is for offset translation

    checking_time = time.time() - start

    if (decreases and bounded):
        print('Hurray! It decreases and it is bounded')
    elif (decreases):
        print('Almost. It decreases but it is not bounded')
    else:
        print('Too bad. That\'s not a ranking function')
        
    return checking_time, decreases, bounded


def run_termination(PROGRAM, CLASS, FUNCTION, loop_offset, SAMPLES, limit, MODEL, learning_function, loss_function,
                    tracing_seed, sampling_strategy="default"):
    # start = time.time()  # process_time excludes the time taken by the traces

    trace, model, decreases, bounded, = None, None, None, None

    # ######### LOOP HEADS #######
    # print(PROGRAM)
    # LOOP_OFFSET = get_loop_heads(file_path + PROGRAM, CLASS, FUNCTION)[0]

    res = {'program': PROGRAM, 'function': FUNCTION, 'class': CLASS, 'learning': None, 'tracing': None, 'checking': None}
    
    try:
        res['tracing'], trace = tracing(PROGRAM, CLASS, FUNCTION, SAMPLES, limit, loop_offset, tracing_seed,
                                        sampling_strategy=sampling_strategy)

    except Exception as e:
        res['error'] = str(e)
        return res

    try:
        res['learning'], model = run_learning(trace, loop_offset, MODEL, learning_function, loss_function)

        model.print_sympy()
        roundweights = model.get_round_weights()[0]
        weights = model.get_weights()[0]
        res['rounderror'] = norm(weights - roundweights, ord=np.inf)
        #max([abs((w - r)/w) for (w,r) in zip(weights, roundweights)])
        #

        # this is implemented in ModelName.print_sympy()
        #symvars = sp.Matrix(sp.symbols(model.input_vars, real=True))
        #symorig = model.get_weights() * symvars
        #symround = model.get_round_weights() * symvars
        #for e in symorig:
        #    print(e)
        #print('After rounding')
        #for e in symround:
        #    print(e)
        print('Error: {}'.format(res['rounderror']))
    except Exception as e:
        res['error'] = str(e)
        return res
    
    try:
        res['checking'], res['decrease'], res['bounded'] = run_checking(PROGRAM, CLASS, FUNCTION, loop_offset, model)
    except Exception as e:
        res['error'] = str(e)
        return res

    return res


