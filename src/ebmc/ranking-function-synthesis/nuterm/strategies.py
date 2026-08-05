import sys
import time
import os
import pathlib
import psutil

import json

import torch

from loopheads import get_loop_heads
from models.SumOfRelu2 import SumOfRelu2

from termination import run_termination
from termination import tracing
from termination import run_learning

from models.SingleLinearWithRelu import SingleLinearWithRelu
from models.SingleLinear import SingleLinear
from models.TwoLayerRelu import TwoLayerRelu
from models.SumOfRelu import SumOfRelu
from models.SumOfLinearsWithLex import SumOfLinearsWithLex

import torch.nn.functional as F

from learning import *

from javachecker import *

import sympy as sp
import numpy as np
from torch import nn

from utils import add_new_traces, get_and_layout_traces, get_and_layout_traces_mvgaussian

import subprocess
import re

tracing_seed = None

processes = psutil.cpu_count(logical=False)


def pos_neg_unary_init(m: torch.nn.Linear):
    lst = []
    for x in m.weight.data:
        l = []
        for y in x:
            if y > 0.2:
                l.append(1.0)
            elif y < -0.2:
                l.append(-1.0)
            else:
                l.append(0.0)
        lst.append(torch.Tensor(l))

    res = torch.stack(lst)
    return res


# ===================================
# - strategies
# ===================================
def anticorr_sumofrelu(vcds, overwrite_sampling=None, seed=None):

    if seed is not None:
        torch.manual_seed(seed)

    print("Running with {}".format(('pairanticorr' if overwrite_sampling is None else overwrite_sampling)))
    try:
        loop_heads = get_loop_heads(jarfile, classname, methodname)
        assert len(loop_heads) <= 2
        #print(loop_heads)
        #loop_offset = loop_heads[0]
    except Exception as e:
        return {'program': jarfile, 'function': methodname, 'class': classname, 'error': str(e)}
    limit = 100
    if force_sample_size is None:
        samples = 1000
    else:
        samples = force_sample_size

    trace, model, decreases, invar, = None, None, None, None
    res = {'program': jarfile, 'function': methodname, 'class': classname,
           'learning': None, 'tracing': None, 'checking': None}
    try:
        res['tracing'], trace = tracing(jarfile, classname, methodname,
                                        samples, limit, loop_heads,
                                        seed, ('pairanticorr' if overwrite_sampling is None else overwrite_sampling),
                                        num_processes=processes)
    except Exception as e:
        return {'program': jarfile, 'function': methodname, 'class': classname, 'error': str(e)}
    input_vars = trace.get_pos_identifiers(frame=5)
    input_dim = len(input_vars)

    input_before = []
    input_after = []

    # creating data and model with info from trace
    
    for head in loop_heads:
        try:
            head_input_before, head_input_after = trace.pair_all_traces_multi_as_tensor(head, loop_heads) # TODO CHANGE THIS
        except RuntimeError as e:
            return {'program': jarfile, 'function': methodname, 'class': classname, 'error': str(e)}

        input_before.append(head_input_before)
        input_after.append(head_input_after)


    #print(input_before[0])
    #print(input_after[0])



    res['checking'] = .0
    res['learning'] = .0
    # Learning
    for t in range(10):

        model = SumOfRelu(len(trace.get_pos_identifiers()),
                          n_out=len(loop_heads),
                          n_summands=5,
                          input_vars=input_vars)
        optimiser = optim.AdamW(model.parameters(), lr=.05)

        print('=' * 40)
        print(' - Learning')
        print('=' * 40)
        learn_start = time.time()
        loss = None

        for iteration in range(1000):
            optimiser.zero_grad()

            output_before = []
            output_after = []
            for i in range(len(loop_heads)):
                output_before.append(model(input_before[i]))
                output_after.append(model(input_after[i]))

            loss = torch.tensor([])
            for i in range(len(loop_heads)):
                for j in range(0, i):
                    loss = torch.cat((loss, F.relu(output_after[j] - output_before[j])[:, j]), 0)
                loss = torch.cat((loss, F.relu(output_after[i] - output_before[i] + 1)[:, i]), 0)

            loss = loss.mean()
            if loss == 0.:
                res["iteration"] = iteration
                break

            loss.backward()
            optimiser.step()

        res['learning'] += time.time() - learn_start
        print("loss: {}".format(loss.item()))


        print('=' * 40)
        print(' - Rounding')
        print('=' * 40)
        S = 1
        W = model.fc1.weight
        for row in W:
            for x in row:
                while (2 * S < abs(x)):
                    S = 2 * S

        if model.fc1.bias is not None:
            b = model.fc1.bias
            for x in b:
                while (2 * S < abs(x)):
                    S = 2 * S
        else:
            b = torch.zeros(model.fc1.out_features)


        W_round = (model.fc1.weight.data.numpy() / S).round()
        b_round = (b.data.numpy() / S).round()

        symvars = sp.Matrix(sp.symbols(input_vars, real=True))
        symorig = (W * symvars + b).applyfunc(sp.Function('relu'))
        symround = (W_round * symvars + b_round).applyfunc(sp.Function('relu'))
        for i, e in enumerate(symorig):
            print(i, e.xreplace({n: round(n, 2) for n in e.atoms(sp.Number)}))
        print('After rounding')
        for i, e in enumerate(symround):
            print(i, e)

        print('=' * 40)
        print(' - Checking')
        print('=' * 40)
        check_start = time.time()

        n_summands = model.n_summands
        lexiW = []
        lexib = []
        lexiout = []
        for i in range(0, len(loop_heads)):
            lexiW.append(W_round[n_summands*i:n_summands*(i+1)])
            lexib.append(b_round[n_summands*i:n_summands*(i+1)])
            lexiout.append(torch.ones(1, n_summands))
        
        res['decrease'], res['invar'], cex = check_sum_of_relu(jarfile, classname, methodname,
                                                                 loop_heads, input_vars,
                                                                 lexiout, lexiW, lexib)

        if (res['decrease']):
            print("Termination was proven.")
            print('YES')
        else:
            print('Not yet.')
            print(cex)

        res['checking'] += time.time() - check_start

        if (res['decrease']):
            break

        print('=' * 40)
        print(' - Randomising')
        print('=' * 40)
        seen = set()
        for i, row in enumerate(W_round):
            row = tuple(row.tolist())
            if row in seen:
                nn.init.normal_(model.fc1.weight[i])
                e = symvars.dot(model.fc1.weight.data.numpy()[i])
                print("reinitialising {} to {}".format(i, e.xreplace(
                    {n: round(n, 2) for n in e.atoms(sp.Number)})))
            else:
                seen.add(row)


    return res



# ===================================
# - strategies
# ===================================
def single_linear_with_relu(vcds, overwrite_sampling=None, strat_args=None):
    print("Running with {}".format(('pairanticorr' if overwrite_sampling is None else overwrite_sampling)))
    try:
        loop_heads = get_loop_heads(jarfile, classname, methodname)
        assert len(loop_heads) <= 2
        print(loop_heads)
        # loop_offset = loop_heads[0]
    except Exception as e:
        return {'program': jarfile, 'function': methodname, 'class': classname, 'error': str(e)}
    limit = 100
    if force_sample_size is None:
        samples = 1000
    else:
        samples = force_sample_size

    trace, model, decreases, bounded, = None, None, None, None
    res = {'program': jarfile, 'function': methodname, 'class': classname,
           'learning': None, 'tracing': None, 'checking': None}

    try:
        res['tracing'], trace = tracing(jarfile, classname, methodname,
                                        samples, limit, loop_heads,
                                        tracing_seed,
                                        ('pairanticorr' if overwrite_sampling is None else overwrite_sampling),
                                        num_processes=processes)
    except Exception as e:
        return {'program': jarfile, 'function': methodname, 'class': classname, 'error': str(e)}

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
            return {'program': jarfile, 'function': methodname, 'class': classname, 'error': str(e)}

        input_before.append(head_input_before)
        input_after.append(head_input_after)
    model = SumOfRelu(len(trace.get_pos_identifiers()),
                      n_out=len(loop_heads),
                      n_summands=1,
                      input_vars=input_vars)

    res['checking'] = .0
    res['learning'] = .0
    # Learning
    optimiser = optim.AdamW(model.parameters(), lr=.05)
    for t in range(2):
        print('=' * 40)
        print(' - Learning')
        print('=' * 40)
        learn_start = time.time()
        loss = None
        for iteration in range(1000):
            optimiser.zero_grad()

            output_before = []
            output_after = []
            for i in range(len(loop_heads)):
                output_before.append(model(input_before[i]))
                output_after.append(model(input_after[i]))

            loss = torch.tensor([])
            for i in range(len(loop_heads)):
                for j in range(0, i):
                    loss = torch.cat((loss, F.relu(output_after[j] - output_before[j])[:, j]), 0)
                loss = torch.cat((loss, F.relu(output_after[i] - output_before[i] + 1)[:, i]), 0)

            loss = loss.mean()
            if loss == 0.:
                res["iteration"] = iteration
                break

            loss.backward()
            optimiser.step()

        res['learning'] += time.time() - learn_start
        print("loss:", loss.item())

        print('=' * 40)
        print(' - Rounding')
        print('=' * 40)
        S = 1
        W = model.fc1.weight
        for row in W:
            for x in row:
                while (2 * S < abs(x)):
                    S = 2 * S

        if model.fc1.bias is not None:
            b = model.fc1.bias
            for x in b:
                while (2 * S < abs(x)):
                    S = 2 * S
        else:
            b = torch.zeros(model.fc1.out_features)

        W_round = (model.fc1.weight.data.numpy() / S).round()
        b_round = (b.data.numpy() / S).round()

        symvars = sp.Matrix(sp.symbols(input_vars, real=True))
        symorig = (W * symvars).applyfunc(sp.Function('relu'))
        symround = (W_round * symvars).applyfunc(sp.Function('relu'))
        for i, e in enumerate(symorig):
            print(i, e.xreplace({n: round(n, 2) for n in e.atoms(sp.Number)}))
        print('After rounding')
        for i, e in enumerate(symround):
            print(i, e)

        print('=' * 40)
        print(' - Checking')
        print('=' * 40)
        check_start = time.time()

        n_summands = model.n_summands
        lexiW = []
        lexib = []
        for i in range(0, len(loop_heads)):
            lexiW.append(W_round[n_summands * i:n_summands * (i + 1)])
            lexib.append(b_round[n_summands * i:n_summands * (i + 1)])

        res['decrease'], res['bounded'], cex = check_sum_of_relu(jarfile, classname, methodname,
                                                            loop_heads, input_vars,
                                                            lexiW, lexib)

        if (res['decrease']):
            print("Termination was proven.")
            print('YES')
        else:
            print('Not yet.')

        res['checking'] += time.time() - check_start

        if (res['decrease']):
            break

        print('=' * 40)
        print(' - Randomising')
        print('=' * 40)
        seen = set()
        for i, row in enumerate(W_round):
            row = tuple(row.tolist())
            if row in seen:
                nn.init.normal_(model.fc1.weight[i])
                e = symvars.dot(model.fc1.weight.data.numpy()[i])
                print("reinitialising {} to {}".format(i, e.xreplace(
                    {n: round(n, 2) for n in e.atoms(sp.Number)})))
            else:
                seen.add(row)

    return res



def i40_rank(vcds, overwrite_sampling=None):
    try:
        loop_heads = get_loop_heads(jarfile, classname, methodname)
        assert len(loop_heads) == 1

        # loop_offset = loop_heads[0]
    except Exception as e:
        return {'program': jarfile, 'function': methodname, 'class': classname, 'error': str(e)}

    limit = None
    if force_sample_size is None:
        samples = 1000
    else:
        samples = force_sample_size
    trace, model, decreases, bounded, = None, None, None, None
    res = {'program': jarfile, 'function': methodname, 'class': classname,
           'learning': None, 'tracing': None, 'checking': None, 'sample_size': samples}

    res['tracing'], trace = tracing(jarfile, classname, methodname,
                                    samples, limit, loop_heads,
                                    tracing_seed,  ('pairanticorr' if overwrite_sampling is None else overwrite_sampling), num_processes=processes)

    input_vars = trace.get_pos_identifiers(frame=5)


    # creating data and model with info from trace

    input_before, input_after = trace.pair_all_traces_multi_as_tensor(loop_heads[0], loop_heads)  # TODO CHANGE THIS

    model = SingleLinearWithRelu(len(trace.get_pos_identifiers()), input_vars=input_vars)
    # model.fc1.weight = torch.nn.Parameter(torch.stack([torch.Tensor([1.0, -1.0])]))
    res['checking'] = .0
    res['learning'] = .0
    # Learning
    optimiser = optim.AdamW(model.parameters(), lr=.05)
    for t in range(2):
        print('=' * 40)
        print(' - Learning')
        print('=' * 40)
        learn_start = time.time()
        loss = None
        for iteration in range(1000):
            optimiser.zero_grad()

            output_before = model(input_before)
            output_after = model(input_after)

            loss = (F.relu(output_after - output_before + 1)).mean()
            # print(t, "loss:", loss.item())
            if loss == 0.:
                res["iteration"] = iteration
                break

            loss.backward()
            optimiser.step()

        res['learning'] += time.time() - learn_start
        print("loss:", loss.item())

        print('=' * 40)
        print(' - Rounding')
        print('=' * 40)
        S = 1
        W = model.fc1.weight

        if model.fc1.bias is not None:
            b = model.fc1.bias
        else:
            b = torch.zeros(model.fc1.out_features)

        W_round = (model.fc1.weight.data.numpy() / S).round()
        b_round = (b.data.numpy() / S).round()

        symvars = sp.Matrix(sp.symbols(input_vars, real=True))
        symorig = (W * symvars).applyfunc(sp.Function('relu'))
        symround = (W_round * symvars).applyfunc(sp.Function('relu'))
        for i, e in enumerate(symorig):
            print(i, e.xreplace({n: round(n, 2) for n in e.atoms(sp.Number)}))
        print('After rounding')
        for i, e in enumerate(symround):
            print(i, e)


        print('=' * 40)
        print(' - Checking')
        print('=' * 40)
        check_start = time.time()


        n_summands = 1
        lexiW = []
        lexib = []
        for i in range(0, len(loop_heads)):
            lexiW.append(W_round[n_summands * i:n_summands * (i + 1)])
            lexib.append(b_round[n_summands * i:n_summands * (i + 1)])

        res['decrease'], res['bounded'], cex = check_sum_of_relu(jarfile, classname, methodname,
                                                            loop_heads, input_vars,
                                                            lexiW, lexib)


        if (not res['decrease']):
            print('Not yet.')
        else:
            print("Termination was proven.")
            print('YES')

        res['checking'] += time.time() - check_start

        if (res['decrease']):
            break

        print('=' * 40)
        print(' - Randomising')
        print('=' * 40)
        seen = set()
        for i, row in enumerate(W_round):
            row = tuple(row.tolist())
            if row in seen:
                nn.init.normal_(model.fc1.weight[i])
                e = symvars.dot(model.fc1.weight.data.numpy()[i])
                print("reinitialising {} to {}".format(i, e.xreplace(
                    {n: round(n, 2) for n in e.atoms(sp.Number)})))
            else:
                seen.add(row)
    return res


# multiply by two before calling .round()
def anticorr_sumofrelu2_cegsloop(vcds, overwrite_sampling=None, seed=None, strat_args=None):
    if seed is not None:
        torch.manual_seed(seed)

    sampling_strategy = "pairanticorr"
    if overwrite_sampling is not None:
        sampling_strategy = overwrite_sampling

    limit = 1000
    if force_sample_size is None:
        samples = 500
    else:
        samples = force_sample_size

    print("Running with {} and {} samples of max length {}.".format(sampling_strategy, samples, limit))
    try:
        loop_heads = get_loop_heads(jarfile, classname, methodname)
        if len(loop_heads) > 2:
            return {'program': jarfile, 'function': methodname, 'class': classname, 'error': "More than two loops"}
    except Exception as e:
        return {'program': jarfile, 'function': methodname, 'class': classname, 'error': str(e)}

    trace, model, decreases, invar, = None, None, None, None
    res = {'program': jarfile, 'function': methodname, 'class': classname, 'supported': None, 'trace_max_length': limit,
           'num_samples': samples}

    tracing_seed = seed

    try:
        r = get_and_layout_traces(jarfile, classname, methodname, samples, limit,
                                  loop_heads, tracing_seed, res, sampling_strategy)

        input_vars, input_before, input_after = r
    except Exception as e:
        print("Probably too few samples.")
        res["error_cause"] = "Sampling did not produce any data pairs."
        return res

    print('first observation: ', input_before[0][0])
    print("vars {}".format(input_vars))

    res["num_pairs"] = list(map(lambda x: x.size()[0], input_before))

    n_loop_heads = len(loop_heads)

    res['checking'] = .0
    res['learning'] = .0
    # Learning

    for t in range(20):

        model = SumOfRelu2(len(input_vars),
                           n_out=n_loop_heads,
                           n_summands=5)
        optimiser = optim.AdamW(model.parameters(), lr=.05)

        print('=' * 40)
        print(' - Learning')
        print('=' * 40)
        learn_start = time.time()
        loss = None
        for x in range(len(loop_heads)):
            print("{} datapoints for head {}".format(input_before[x].size()[0], x))

        for iteration in range(1000):

            optimiser.zero_grad()

            loss = torch.tensor([])
            for i in range(n_loop_heads):
                output_before = model(input_before[i])
                output_after = model(input_after[i])
                loss = torch.cat((loss, F.relu(output_after[i] - output_before[i] + 1)), 0)
                for j in range(0, i):
                    loss = torch.cat((loss, F.relu(output_after[j] - output_before[j])), 0)

            loss = loss.mean()
            #print("loss: {}".format(loss.item()))
            if loss == 0.:
                res["iteration"] = iteration
                break

            loss.backward()
            optimiser.step()

        res['learning'] += time.time() - learn_start
        print("loss:", loss.item())

        Ses = [.5, 1.]

        for S in Ses:
            print('=' * 40)
            print(' - Rounding with S =', S)
            print('=' * 40)

            W_to_check = []
            b_to_check = []
            out_to_check = []
            for i in range(len(loop_heads)):
                print('  ' + '=' * 38)
                print('   - Lexicographic function ' + str(i))
                print('  ' + '=' * 38)
                W = model.fc1[i].weight
                if model.fc1[i].bias is not None:
                    b = model.fc1[i].bias
                else:
                    b = torch.zeros(model.fc1[i].out_features)
                out = model.fc2[i].weight

                W_round = (W.data.numpy() / S).round()
                b_round = (b.data.numpy() / S).round()
                out_round = (out.data.numpy() / S).round()

                symvars = sp.Matrix(sp.symbols(input_vars, real=True))
                symorig = (W * symvars + b[:, None]).applyfunc(sp.Function('relu'))
                symround = (W_round * symvars + b_round[:, None]).applyfunc(sp.Function('relu'))
                # print(out[0,1].item())
                for j, e in enumerate(symorig):
                    print('  ', j,
                          (round(out[0, j].item(), 2) * e).xreplace({n: round(n, 2) for n in e.atoms(sp.Number)}))
                print('  After rounding')
                for j, e in enumerate(symround):
                    print('  ', j, (out_round[0, j] * e))

                W_to_check.append(W_round)
                b_to_check.append(b_round)
                out_to_check.append(out_round)

            print('  ' + '=' * 40)
            print('   - Checking')
            print('  ' + '=' * 40)
            check_start = time.time()

            try:
                res['decrease'], res['invar'], cex = check_sum_of_relu(jarfile, classname, methodname,
                                                                       loop_heads, input_vars,
                                                                       out_to_check, W_to_check, b_to_check)
            except RuntimeError as e:
                res.pop('checking')
                res['error'] = str(e)
                return res

            if res['decrease']:
                print("Termination was proven.")
                print('YES')
                break
            else:
                print('Not yet.')
                print(cex)

                if not cex == {}:

                    dt = {"arguments": []}
                    for x in input_vars:
                        if x in cex:
                            dt["arguments"].append(cex[x])

                    r = None
                    res_tmp = res
                    try:

                        cegs_file = "cex.json"
                        with open(cegs_file, "w+") as f:
                            json.dump(dt, f)
                        cegs_samples=100
                        r = add_new_traces(input_before, input_after, jarfile, classname, methodname, cegs_samples, limit,
                                                  loop_heads, tracing_seed, res, cegs_file=cegs_file)
                        input_vars, input_before, input_after = r
                    except Exception as e:
                        print(e)
                        print("CEGS loop did not produce usable samples.")
                        res = res_tmp



        res['checking'] += time.time() - check_start

        if (res['decrease']):
            break

        print('=' * 40)
        print(' - Randomising')
        print('=' * 40)
        for i in range(0, n_loop_heads):
            print('  ' + '=' * 38)
            print('   - Lexicographic function ' + str(i))
            print('  ' + '=' * 38)
            seen = set()
            for j, row in enumerate(W_round):
                row = tuple(row.tolist())
                if row in seen:
                    nn.init.normal_(model.fc1[i].weight[j])
                    e = symvars.dot(model.fc1[i].weight.data.numpy()[j])
                    print("   reinitialising {} to {}".format(j, e.xreplace(
                        {n: round(n, 2) for n in e.atoms(sp.Number)})))
                else:
                    seen.add(row)

    return res


def check_ranking_function(verilog_files, candidate):
    check_cmd = ['ebmc', '--verbosity', '0', '--json-result', '/dev/stdout',
            '--ranking-function', candidate]
    check_cmd.extend(verilog_files)
    result = subprocess.run(check_cmd, universal_newlines=True,
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if result.returncode == 10:
        return False
    print(result.stdout)
    result.check_returncode()
    json_result = json.loads(result.stdout)
    return json_result["properties"][0]["status"] == "PROVED"


def anticorr_sumofrelu2(verilog_files, vcds, overwrite_sampling=None, seed=None, strat_args=None):
    if seed is not None:
        torch.manual_seed(seed)

    sampling_strategy = "pairanticorr"
    if overwrite_sampling is not None:
        sampling_strategy = overwrite_sampling

    limit = 1000
    samples = len(vcds)

    print("Running with {} and {} samples of max length {}.".format(sampling_strategy, samples, limit))
    trace, model, decreases, invar, = None, None, None, None
    res = {'supported': None, 'trace_max_length': limit, 'num_samples': samples}

    tracing_seed = seed

    r = get_and_layout_traces(vcds, limit, tracing_seed, res)

    input_vars, input_before, input_after = r

    #print('first observation: ', input_before[0][0])
    #print("vars {}".format(input_vars))

    res["num_pairs"] = list(map(lambda x: x.size()[0], input_before))

    n_loop_heads = 1

    res['checking'] = .0
    res['learning'] = .0
    # Learning

    for t in range(20):

        model = SumOfRelu2(len(input_vars),
                           n_out=n_loop_heads,
                           n_summands=2)
        optimiser = optim.AdamW(model.parameters(), lr=.05)

        print('=' * 40)
        print(' - Learning')
        print('=' * 40)
        learn_start = time.time()
        loss = None
        for iteration in range(1000):

            optimiser.zero_grad()

            # output_before = []
            # output_after = []
            # for i in range(len(loop_heads)):
            #     output_before.append(model(input_before[i]))
            #     output_after.append(model(input_after[i]))

            loss = torch.tensor([])
            for i in range(n_loop_heads):
                output_before = model(input_before[i])
                output_after = model(input_after[i])
                loss = torch.cat((loss, F.relu(output_after[i] - output_before[i] + 1)), 0)
                for j in range(0, i):
                    loss = torch.cat((loss, F.relu(output_after[j] - output_before[j])), 0)

            loss = loss.mean()
            if iteration % 100 == 0:
                print("loss at iteration {}: {}".format(iteration, loss.item()))
            if loss == 0.:
                res["iteration"] = iteration
                break

            loss.backward()
            optimiser.step()

        res['learning'] += time.time() - learn_start
        print("loss:", loss.item())

        Ses = [2, 1]

        for S in Ses:
            print('=' * 40)
            print(' - Rounding with S =', S)
            print('=' * 40)

            W_to_check = []
            b_to_check = []
            out_to_check = []
            # for i in range(len(loop_heads)):
            i = 0
            print('  ' + '=' * 38)
            print('   - Lexicographic function ' + str(i))
            print('  ' + '=' * 38)
            W = model.fc1[i].weight
            if model.fc1[i].bias is not None:
                b = model.fc1[i].bias
            else:
                b = torch.zeros(model.fc1[i].out_features)
            out = model.fc2[i].weight

            W_round = (W.data.numpy() * S).round().astype(int)
            b_round = (b.data.numpy() * S).round().astype(int)
            out_round = (out.data.numpy() * S).round().astype(int)

            print(input_vars)
            symvars = sp.Matrix(sp.symbols(input_vars, real=False))
            symorig = (W * symvars + b[:, None]) #.applyfunc(sp.Function('relu'))
            symround = sp.simplify(W_round * symvars + b_round[:, None]) #.applyfunc(sp.Function('relu'))
            print(out[0,1].item())
            for j, e in enumerate(symorig):
                print('  ', j,
                      (round(out[0, j].item(), 2) * e).xreplace({n: round(n, 2) for n in e.atoms(sp.Number)}))
            print('  After rounding')
            for j, e in enumerate(symround):
                print('  ', j, (out_round[0, j] * e))
            linear_combination = sp.simplify(sum([(out_round[0, j] * e) for j, e in
                enumerate(symround)], 0))

            print(linear_combination)

            W_to_check.append(W_round)
            b_to_check.append(b_round)
            out_to_check.append(out_round)

            print('  ' + '=' * 40)
            print('   - Checking')
            print('  ' + '=' * 40)
            check_start = time.time()

            try:
                print("input_vars: ", input_vars)
                print("out_to_check: ", out_to_check)
                print("W_to_check: ", W_to_check)
                print("b_to_check: ", b_to_check)
                ##
                ##fun = []
                ##for W,b in zip(W_to_check, b_to_check):

                ##    assert np.shape(W)[0] == np.shape(b)[0]
                ##    SOR = []
                ##    for i in range(0, np.shape(W)[0]):
                ##        SOR.append([int(x) for x in W[i,:]] + [int(b[i])])
                ##    fun.append(SOR)

                ##print("fun: ", fun)
                ##fun_str = "0";
                ##for layer in fun[0]:
                ##    fun_str += " + (0";
                ##    for (coeff, var) in zip(layer, input_vars):
                ##        fun_str += " + " + str(coeff) + " * " + var
                ##    fun_str += ")"
                ##print("FUN: ", fun_str)
                # out = [[int(x) for x in W[0,:]] for W in out_to_check]
                # hidden = [[row for row in relus] for relus in fun]
                # print("out:", out)
                # print("hidden:", hidden)
                ##
                # rewritten_relu = re.sub(r'relu\(([^\)]+)\)', r'(\1 > 0 ? \1 : 0)',
                #         str(linear_combination))
                rewritten_relu = str(linear_combination)
                if rewritten_relu.startswith('-'):
                    rewritten_relu = "0 " + rewritten_relu
                res['decrease'] = check_ranking_function(verilog_files,
                        rewritten_relu)
            except RuntimeError as e:
                res.pop('checking')
                res['error'] = str(e)
                return res

            if res['decrease']:
                print("Liveness was proven using ranking function",
                        rewritten_relu, "in iteration", t)
                print('YES')
                break
            else:
                print(rewritten_relu, "is not a ranking function")
                print('Not yet.')

        res['checking'] += time.time() - check_start

        if (res['decrease']):
            break

        print('=' * 40)
        print(' - Randomising')
        print('=' * 40)
        for i in range(0, n_loop_heads):
            print('  ' + '=' * 38)
            print('   - Lexicographic function ' + str(i))
            print('  ' + '=' * 38)
            seen = set()
            for j, row in enumerate(W_round):
                row = tuple(row.tolist())
                if row in seen:
                    nn.init.normal_(model.fc1[i].weight[j])
                    e = symvars.dot(model.fc1[i].weight.data.numpy()[j])
                    print("   reinitialising {} to {}".format(j, e.xreplace(
                        {n: round(n, 2) for n in e.atoms(sp.Number)})))
                else:
                    seen.add(row)

    return res


def anticorr_sumoflinears_or_concat(verilog_files, vcds, overwrite_sampling=None, seed=None, strat_args=None):
    if seed is not None:
        torch.manual_seed(seed)

    sampling_strategy = "pairanticorr"
    if overwrite_sampling is not None:
        sampling_strategy = overwrite_sampling

    limit = 1000
    samples = len(vcds)

    print("Running with {} and {} samples of max length {}.".format(sampling_strategy, samples, limit))
    trace, model, decreases, invar, = None, None, None, None
    res = {'supported': None, 'trace_max_length': limit, 'num_samples': samples}

    tracing_seed = seed

    r = get_and_layout_traces(vcds, limit, tracing_seed, res)

    input_vars, input_before, input_after = r

    #print('first observation: ', input_before[0][0])
    #print("vars {}".format(input_vars))

    res["num_pairs"] = list(map(lambda x: x.size()[0], input_before))

    n_loop_heads = 1

    res['checking'] = .0
    res['learning'] = .0
    # Learning

    for t in range(200):

        model = SumOfLinearsWithLex(len(input_vars),
                           n_out=n_loop_heads,
                           n_summands=2)
        optimiser = optim.AdamW(model.parameters(), lr=.05)

        print('=' * 40)
        print(' - Learning')
        print('=' * 40)
        learn_start = time.time()
        loss = None
        for iteration in range(1000):

            optimiser.zero_grad()

            # output_before = []
            # output_after = []
            # for i in range(len(loop_heads)):
            #     output_before.append(model(input_before[i]))
            #     output_after.append(model(input_after[i]))

            loss = torch.tensor([])
            for i in range(n_loop_heads):
                output_before = model(input_before[i])
                output_after = model(input_after[i])
                loss = torch.cat((loss, F.relu(output_after[i] - output_before[i] + 1)), 0)
                for j in range(0, i):
                    loss = torch.cat((loss, F.relu(output_after[j] - output_before[j])), 0)

            loss = loss.mean()
            if iteration % 100 == 0:
                print("loss at iteration {}: {}".format(iteration, loss.item()))
            if loss == 0.:
                res["iteration"] = iteration
                break

            loss.backward()
            optimiser.step()

        res['learning'] += time.time() - learn_start
        print("loss:", loss.item())

        Ses = [2, 1]

        for S in Ses:
            print('=' * 40)
            print(' - Rounding with S =', S)
            print('=' * 40)

            W_to_check = []
            b_to_check = []
            out_to_check = []
            # for i in range(len(loop_heads)):
            i = 0
            print('  ' + '=' * 38)
            print('   - Lexicographic function ' + str(i))
            print('  ' + '=' * 38)
            # W = model.fc1[i].weight
            # if model.fc1[i].bias is not None:
            #     b = model.fc1[i].bias
            # else:
            #     b = torch.zeros(model.fc1[i].out_features)
            # out = model.fc2[i].weight
            W = model.fc1.weight
            if model.fc1.bias is not None:
                b = model.fc1.bias
            else:
                b = torch.zeros(model.fc1.out_features)

            W_round = (W.data.numpy() * S).round().astype(int)
            b_round = (b.data.numpy() * S).round().astype(int)
            # out_round = (out.data.numpy() * S).round().astype(int)

            print(input_vars)
            symvars = sp.Matrix(sp.symbols(input_vars, real=False))
            symorig = (W * symvars + b[:, None]) #.applyfunc(sp.Function('relu'))
            symround = sp.simplify(W_round * symvars + b_round[:, None]) #.applyfunc(sp.Function('relu'))
            # print(out[0,1].item())
            # for j, e in enumerate(symorig):
            #     print('  ', j,
            #           (round(out[0, j].item(), 2) * e).xreplace({n: round(n, 2) for n in e.atoms(sp.Number)}))
            print('  After rounding')
            # for j, e in enumerate(symround):
            #     print('  ', j, (out_round[0, j] * e))
            # linear_combination = sum([(out_round[0, j] * e) for j, e in
            #     enumerate(symround)], 0)
            linear_combination = sp.simplify(sum([e for j, e in
                enumerate(symround)], 0))

            print(linear_combination)

            W_to_check.append(W_round)
            b_to_check.append(b_round)
            # out_to_check.append(out_round)

            print('  ' + '=' * 40)
            print('   - Checking')
            print('  ' + '=' * 40)
            check_start = time.time()

            try:
                res['decrease'] = False

                print("input_vars: ", input_vars)
                # print("out_to_check: ", out_to_check)
                print("W_to_check: ", W_to_check)
                print("b_to_check: ", b_to_check)

                concat_operands = []
                for l in W_to_check[0]:
                    for j, v in enumerate(l):
                        if v != 0:
                            concat_operands.append(str(symvars[j]))
                if len(concat_operands):
                    concat_str = "{" + ",".join(concat_operands) + "}"
                    res['decrease'] = check_ranking_function(verilog_files,
                            concat_str)

                ##
                ##fun = []
                ##for W,b in zip(W_to_check, b_to_check):

                ##    assert np.shape(W)[0] == np.shape(b)[0]
                ##    SOR = []
                ##    for i in range(0, np.shape(W)[0]):
                ##        SOR.append([int(x) for x in W[i,:]] + [int(b[i])])
                ##    fun.append(SOR)

                ##print("fun: ", fun)
                ##fun_str = "0";
                ##for layer in fun[0]:
                ##    fun_str += " + (0";
                ##    for (coeff, var) in zip(layer, input_vars):
                ##        fun_str += " + " + str(coeff) + " * " + var
                ##    fun_str += ")"
                ##print("FUN: ", fun_str)
                # out = [[int(x) for x in W[0,:]] for W in out_to_check]
                # hidden = [[row for row in relus] for relus in fun]
                # print("out:", out)
                # print("hidden:", hidden)
                ##
                # rewritten_relu = re.sub(r'relu\(([^\)]+)\)', r'(\1 > 0 ? \1 : 0)',
                #         str(linear_combination))
                if not res['decrease']:
                    rewritten_relu = str(linear_combination)
                    if rewritten_relu.startswith('-'):
                        rewritten_relu = "0 " + rewritten_relu
                    res['decrease'] = check_ranking_function(verilog_files,
                            rewritten_relu)
                else:
                    rewritten_relu = concat_str

            except RuntimeError as e:
                res.pop('checking')
                res['error'] = str(e)
                return res

            if res['decrease']:
                print("Liveness was proven using ranking function",
                        rewritten_relu, "in iteration", t)
                print('YES')
                break
            else:
                print(rewritten_relu, "is not a ranking function")
                print('Not yet.')

        res['checking'] += time.time() - check_start

        if (res['decrease']):
            break

        print('=' * 40)
        print(' - Randomising')
        print('=' * 40)
        for i in range(0, n_loop_heads):
            print('  ' + '=' * 38)
            print('   - Lexicographic function ' + str(i))
            print('  ' + '=' * 38)
            seen = set()
            for j, row in enumerate(W_round):
                row = tuple(row.tolist())
                if row in seen:
                    nn.init.normal_(model.fc1.weight[j])
                    e = symvars.dot(model.fc1.weight.data.numpy()[j])
                    print("   reinitialising {} to {}".format(j, e.xreplace(
                        {n: round(n, 2) for n in e.atoms(sp.Number)})))
                else:
                    seen.add(row)

    return res


# anticorr_sumofrelu2 with 10 nodes
def anticorr_sumofrelu_dynamic_nodes(vcds, overwrite_sampling=None, seed=None, strat_args=None):
    if seed is not None:
        torch.manual_seed(seed)

    try:
        n_summds = int(strat_args.split("=")[1])
    except Exception as e:
        print("Could not get number of summands from strat argument.")
        raise e

    sampling_strategy = "pairanticorr"
    if overwrite_sampling is not None:
        sampling_strategy = overwrite_sampling

    limit = 1000
    if force_sample_size is None:
        samples = 1000
    else:
        samples = force_sample_size

    print("Running with {} and {} samples of max length {} with {} nodes in the NN.".format(sampling_strategy, samples,
                                                                                            limit, n_summds))
    try:
        loop_heads = get_loop_heads(jarfile, classname, methodname)
        if len(loop_heads) > 2:
            return {'program': jarfile, 'function': methodname, 'class': classname, 'error': "More than two loops"}
    except Exception as e:
        return {'program': jarfile, 'function': methodname, 'class': classname, 'error': str(e)}

    trace, model, decreases, invar, = None, None, None, None
    res = {'program': jarfile, 'function': methodname, 'class': classname, 'supported': None, 'trace_max_length': limit,
           'num_samples': samples, 'nn_nodes': n_summds}

    tracing_seed = seed

    try:
        r = get_and_layout_traces(jarfile, classname, methodname, samples, limit,
                                  loop_heads, tracing_seed, res, sampling_strategy)

        input_vars, input_before, input_after = r
    except Exception as e:
        print("Probably too few samples.")
        res["error_cause"] = "Sampling did not produce any data pairs."
        return res

    print('first observation: ', input_before[0][0])
    print("vars {}".format(input_vars))

    res["num_pairs"] = list(map(lambda x: x.size()[0], input_before))

    n_loop_heads = len(loop_heads)

    res['checking'] = .0
    res['learning'] = .0
    # Learning

    for t in range(20):

        model = SumOfRelu2(len(input_vars),
                           n_out=n_loop_heads,
                           n_summands=n_summds)
        optimiser = optim.AdamW(model.parameters(), lr=.05)

        print('=' * 40)
        print(' - Learning')
        print('=' * 40)
        learn_start = time.time()
        loss = None
        for iteration in range(1000):

            optimiser.zero_grad()

            # output_before = []
            # output_after = []
            # for i in range(len(loop_heads)):
            #     output_before.append(model(input_before[i]))
            #     output_after.append(model(input_after[i]))

            loss = torch.tensor([])
            for i in range(n_loop_heads):
                output_before = model(input_before[i])
                output_after = model(input_after[i])
                loss = torch.cat((loss, F.relu(output_after[i] - output_before[i] + 1)), 0)
                for j in range(0, i):
                    loss = torch.cat((loss, F.relu(output_after[j] - output_before[j])), 0)

            loss = loss.mean()
            print("loss: {}".format(loss.item()))
            if loss == 0.:
                res["iteration"] = iteration
                break

            loss.backward()
            optimiser.step()

        res['learning'] += time.time() - learn_start
        print("loss:", loss.item())

        Ses = [1., .5]

        for S in Ses:
            print('=' * 40)
            print(' - Rounding with S =', S)
            print('=' * 40)

            W_to_check = []
            b_to_check = []
            out_to_check = []
            for i in range(len(loop_heads)):
                print('  ' + '=' * 38)
                print('   - Lexicographic function ' + str(i))
                print('  ' + '=' * 38)
                W = model.fc1[i].weight
                if model.fc1[i].bias is not None:
                    b = model.fc1[i].bias
                else:
                    b = torch.zeros(model.fc1[i].out_features)
                out = model.fc2[i].weight

                W_round = (W.data.numpy() / S).round()
                b_round = (b.data.numpy() / S).round()
                out_round = (out.data.numpy() / S).round()

                symvars = sp.Matrix(sp.symbols(input_vars, real=True))
                symorig = (W * symvars + b[:, None]).applyfunc(sp.Function('relu'))
                symround = (W_round * symvars + b_round[:, None]).applyfunc(sp.Function('relu'))
                # print(out[0,1].item())
                for j, e in enumerate(symorig):
                    print('  ', j,
                          (round(out[0, j].item(), 2) * e).xreplace({n: round(n, 2) for n in e.atoms(sp.Number)}))
                print('  After rounding')
                for j, e in enumerate(symround):
                    print('  ', j, (out_round[0, j] * e))

                W_to_check.append(W_round)
                b_to_check.append(b_round)
                out_to_check.append(out_round)

            print('  ' + '=' * 40)
            print('   - Checking')
            print('  ' + '=' * 40)
            check_start = time.time()

            try:
                res['decrease'], res['invar'], cex = check_sum_of_relu(jarfile, classname, methodname,
                                                                       loop_heads, input_vars,
                                                                       out_to_check, W_to_check, b_to_check)
            except RuntimeError as e:
                res.pop('checking')
                res['error'] = str(e)
                return res

            if res['decrease']:
                print("Termination was proven.")
                print('YES')
                break
            else:
                print('Not yet.')
                print(cex)

        res['checking'] += time.time() - check_start

        if (res['decrease']):
            break

        print('=' * 40)
        print(' - Randomising')
        print('=' * 40)
        for i in range(0, n_loop_heads):
            print('  ' + '=' * 38)
            print('   - Lexicographic function ' + str(i))
            print('  ' + '=' * 38)
            seen = set()
            for j, row in enumerate(W_round):
                row = tuple(row.tolist())
                if row in seen:
                    nn.init.normal_(model.fc1[i].weight[j])
                    e = symvars.dot(model.fc1[i].weight.data.numpy()[j])
                    print("   reinitialising {} to {}".format(j, e.xreplace(
                        {n: round(n, 2) for n in e.atoms(sp.Number)})))
                else:
                    seen.add(row)

    return res


# multiply by two before calling .round()
def anticorr_sumofrelu2_gaussian(vcds, overwrite_sampling=None, seed=None, strat_args=None):
    if seed is not None:
        torch.manual_seed(seed)

    limit = 1000
    if force_sample_size is None:
        samples = 1000
    else:
        samples = force_sample_size

    print("Running with {} and {} samples".format('mvgaussian' if overwrite_sampling is None else overwrite_sampling,
                                                  samples))
    try:
        loop_heads = get_loop_heads(jarfile, classname, methodname)
        if (len(loop_heads) > 2):
            return {'program': jarfile, 'function': methodname, 'class': classname, 'error': "More than two loops"}
    except Exception as e:
        return {'program': jarfile, 'function': methodname, 'class': classname, 'error': str(e)}

    trace, model, decreases, invar, = None, None, None, None
    res = {'program': jarfile, 'function': methodname, 'class': classname, 'supported': None}

    tracing_seed = seed

    try:
        input_vars, input_before, input_after = get_and_layout_traces_mvgaussian(jarfile, classname, methodname,
                                                                                 samples, limit, loop_heads,
                                                                                 tracing_seed, res)
    except Exception as e:
        res['error'] = str(e)
        return res

    print('first observation: ', input_before[0][0])

    n_loop_heads = len(loop_heads)

    res['checking'] = .0
    res['learning'] = .0
    # Learning
    for t in range(10):

        model = SumOfRelu2(len(input_vars),
                           n_out=n_loop_heads,
                           n_summands=10)
        optimiser = optim.AdamW(model.parameters(), lr=.05)

        print('=' * 40)
        print(' - Learning')
        print('=' * 40)
        learn_start = time.time()
        loss = None
        for iteration in range(1000):
            optimiser.zero_grad()

            # output_before = []
            # output_after = []
            # for i in range(len(loop_heads)):
            #     output_before.append(model(input_before[i]))
            #     output_after.append(model(input_after[i]))

            loss = torch.tensor([])
            for i in range(n_loop_heads):
                output_before = model(input_before[i])
                output_after = model(input_after[i])
                loss = torch.cat((loss, F.relu(output_after[i] - output_before[i] + 1)), 0)
                for j in range(0, i):
                    loss = torch.cat((loss, F.relu(output_after[j] - output_before[j])), 0)

            loss = loss.mean()
            if loss == 0.:
                res["iteration"] = iteration
                break

            loss.backward()
            optimiser.step()

        res['learning'] += time.time() - learn_start
        print("loss:", loss.item())

        Ses = [.5, 1.]

        for S in Ses:
            print('=' * 40)
            print(' - Rounding with S =', S)
            print('=' * 40)

            W_to_check = []
            b_to_check = []
            out_to_check = []
            for i in range(len(loop_heads)):
                print('  ' + '=' * 38)
                print('   - Lexicographic function ' + str(i))
                print('  ' + '=' * 38)
                W = model.fc1[i].weight
                if model.fc1[i].bias is not None:
                    b = model.fc1[i].bias
                else:
                    b = torch.zeros(model.fc1[i].out_features)
                out = model.fc2[i].weight

                W_round = (W.data.numpy() / S).round()
                b_round = (b.data.numpy() / S).round()
                out_round = (out.data.numpy() / S).round()

                symvars = sp.Matrix(sp.symbols(input_vars, real=True))
                symorig = (W * symvars + b[:, None]).applyfunc(sp.Function('relu'))
                symround = (W_round * symvars + b_round[:, None]).applyfunc(sp.Function('relu'))
                # print(out[0,1].item())
                for j, e in enumerate(symorig):
                    print('  ', j,
                          (round(out[0, j].item(), 2) * e).xreplace({n: round(n, 2) for n in e.atoms(sp.Number)}))
                print('  After rounding')
                for j, e in enumerate(symround):
                    print('  ', j, (out_round[0, j] * e))

                W_to_check.append(W_round)
                b_to_check.append(b_round)
                out_to_check.append(out_round)

            print('  ' + '=' * 40)
            print('   - Checking')
            print('  ' + '=' * 40)
            check_start = time.time()

            try:
                res['decrease'], res['invar'], cex = check_sum_of_relu(jarfile, classname, methodname,
                                                                       loop_heads, input_vars,
                                                                       out_to_check, W_to_check, b_to_check)
            except RuntimeError as e:
                res.pop('checking')
                res['error'] = str(e)
                return res

            if res['decrease']:
                print("Termination was proven.")
                print('YES')
                break
            else:
                print('Not yet.')
                print(cex)

        res['checking'] += time.time() - check_start

        if (res['decrease']):
            break

        print('=' * 40)
        print(' - Randomising')
        print('=' * 40)
        for i in range(0, n_loop_heads):
            print('  ' + '=' * 38)
            print('   - Lexicographic function ' + str(i))
            print('  ' + '=' * 38)
            seen = set()
            for j, row in enumerate(W_round):
                row = tuple(row.tolist())
                if row in seen:
                    nn.init.normal_(model.fc1[i].weight[j])
                    e = symvars.dot(model.fc1[i].weight.data.numpy()[j])
                    print("   reinitialising {} to {}".format(j, e.xreplace(
                        {n: round(n, 2) for n in e.atoms(sp.Number)})))
                else:
                    seen.add(row)

    return res


def anticorr_sumofrelu_baseline(vcds, overwrite_sampling=None, seed=None, strat_args=None):
    if seed is not None:
        torch.manual_seed(seed)

    print("Running with {}".format(('pairanticorr' if overwrite_sampling is None else overwrite_sampling)))
    try:
        loop_heads = get_loop_heads(jarfile, classname, methodname)
        if (len(loop_heads) > 2):
            return {'program': jarfile, 'function': methodname, 'class': classname, 'error': "More than two loops"}
    except Exception as e:
        return {'program': jarfile, 'function': methodname, 'class': classname, 'error': str(e)}

    limit = 100
    if force_sample_size is None:
        samples = 1000
    else:
        samples = force_sample_size

    trace, model, decreases, invar, = None, None, None, None
    res = {'program': jarfile, 'function': methodname, 'class': classname, 'supported': None}

    tracing_seed = seed

    try:
        input_vars, input_before, input_after = get_and_layout_traces(jarfile, classname, methodname,
                                                                      samples, limit, loop_heads, tracing_seed, res)
    except Exception as e:
        res['error'] = str(e)
        return res

    print('first observation: ', input_before[0][0])

    n_loop_heads = len(loop_heads)

    res['checking'] = .0
    res['learning'] = .0
    # Learning
    for t in range(10):

        model = SumOfRelu2(len(input_vars),
                           n_out=n_loop_heads,
                           n_summands=1)
        optimiser = optim.AdamW(model.parameters(), lr=.05)

        print('=' * 40)
        print(' - Learning')
        print('=' * 40)
        learn_start = time.time()
        loss = None
        for iteration in range(1000):
            optimiser.zero_grad()

            # output_before = []
            # output_after = []
            # for i in range(len(loop_heads)):
            #     output_before.append(model(input_before[i]))
            #     output_after.append(model(input_after[i]))

            loss = torch.tensor([])
            for i in range(n_loop_heads):
                output_before = model(input_before[i])
                output_after = model(input_after[i])
                loss = torch.cat((loss, F.relu(output_after[i] - output_before[i] + 1)), 0)
                for j in range(0, i):
                    loss = torch.cat((loss, F.relu(output_after[j] - output_before[j])), 0)

            loss = loss.mean()
            if loss == 0.:
                res["iteration"] = iteration
                break
            loss.backward()
            optimiser.step()

        res['learning'] += time.time() - learn_start
        print("loss:", loss.item())

        Ses = [.5, 1.]

        for S in Ses:
            print('=' * 40)
            print(' - Rounding with S =', S)
            print('=' * 40)

            W_to_check = []
            b_to_check = []
            out_to_check = []
            for i in range(len(loop_heads)):
                print('  ' + '=' * 38)
                print('   - Lexicographic function ' + str(i))
                print('  ' + '=' * 38)
                W = model.fc1[i].weight
                if model.fc1[i].bias is not None:
                    b = model.fc1[i].bias
                else:
                    b = torch.zeros(model.fc1[i].out_features)
                out = model.fc2[i].weight

                W_round = (W.data.numpy() / S).round()
                b_round = (b.data.numpy() / S).round()
                out_round = (out.data.numpy() / S).round()

                symvars = sp.Matrix(sp.symbols(input_vars, real=True))
                symorig = (W * symvars + b[:, None]).applyfunc(sp.Function('relu'))
                symround = (W_round * symvars + b_round[:, None]).applyfunc(sp.Function('relu'))
                # print(out[0,1].item())
                for j, e in enumerate(symorig):
                    print('  ', j,
                          (round(out[0, j].item(), 2) * e).xreplace({n: round(n, 2) for n in e.atoms(sp.Number)}))
                print('  After rounding')
                for j, e in enumerate(symround):
                    print('  ', j, (out_round[0, j] * e))

                W_to_check.append(W_round)
                b_to_check.append(b_round)
                out_to_check.append(out_round)

            print('  ' + '=' * 40)
            print('   - Checking')
            print('  ' + '=' * 40)
            check_start = time.time()

            try:
                res['decrease'], res['invar'], cex = check_sum_of_relu(jarfile, classname, methodname,
                                                                       loop_heads, input_vars,
                                                                       out_to_check, W_to_check, b_to_check)
            except RuntimeError as e:
                res.pop('checking')
                res['error'] = str(e)
                return res

            if res['decrease']:
                print("Termination was proven.")
                print('YES')
                break
            else:
                print('Not yet.')
                print(cex)

        res['checking'] += time.time() - check_start

        if (res['decrease']):
            break

        print('=' * 40)
        print(' - Randomising')
        print('=' * 40)
        for i in range(0, n_loop_heads):
            print('  ' + '=' * 38)
            print('   - Lexicographic function ' + str(i))
            print('  ' + '=' * 38)
            seen = set()
            for j, row in enumerate(W_round):
                row = tuple(row.tolist())
                if row in seen:
                    nn.init.normal_(model.fc1[i].weight[j])
                    e = symvars.dot(model.fc1[i].weight.data.numpy()[j])
                    print("   reinitialising {} to {}".format(j, e.xreplace(
                        {n: round(n, 2) for n in e.atoms(sp.Number)})))
                else:
                    seen.add(row)

    return res

