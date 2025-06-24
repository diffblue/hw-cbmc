import os
import pathlib

import matplotlib.pyplot as plt
from datetime import datetime
import matplotlib.ticker as mtick
from matplotlib.ticker import PercentFormatter
import json
import torch
import io
import json
import os
import numpy as np

from strategies import anticorr_sumofrelu, single_linear_with_relu, anticorr_sumofrelu2_cegsloop, anticorr_sumofrelu2,\
    anticorr_sumofrelu_baseline, anticorr_sumofrelu2_gaussian, anticorr_sumofrelu_dynamic_nodes, anticorr_sumoflinears_or_concat



# =======================================
# - initialise classpath
# =======================================
## file_path = str(pathlib.Path(__file__).parent.absolute())
## os.environ['CLASSPATH'] = file_path + "/../libs/share/java/com.microsoft.z3.jar" + ':' + ':'.join(
##     [e.path for e in os.scandir(file_path + '/../libs/')])
## os.environ['LD_LIBRARY_PATH'] = file_path + "/../libs/lib/"

import argparse
import random
import glob


strategies = {
              "None": anticorr_sumofrelu2,
              "anticorr_sumofrelu" : anticorr_sumofrelu,
              "single_linear_with_relu": single_linear_with_relu,
              "anticorr_sumoflinears_or_concat": anticorr_sumoflinears_or_concat,
              "anticorr_sumofrelu2": anticorr_sumofrelu2,
              "anticorr_sumofrelu_baseline": anticorr_sumofrelu_baseline,
              "anticorr_sumofrelu2_gaussian" : anticorr_sumofrelu2_gaussian,
              "anticorr_sumofrelu2_cegsloop" : anticorr_sumofrelu2_cegsloop,
              "anticorr_sumofrelu_dynamic_nodes": anticorr_sumofrelu_dynamic_nodes,
}


def main(args):

    if args.seed is not None:
        torch.manual_seed(args.seed)
        random.seed(args.seed)
        np.random.seed(args.seed)
        # maybe not
        torch.use_deterministic_algorithms(True)

    strategy = strategies[args.strategy]

    vcds = glob.glob(args.vcd_prefix + '*')

    print("Running {} on VCD-formatted traces {}".format(args.strategy,
        vcds))

    res = None
    if args.strat_args is not None:
        res = strategy(args.verilog, vcds, seed=args.seed, strat_args=args.strat_args)
    else:
        res = strategy(args.verilog, vcds, seed=args.seed)
    return
    res["strategy"] = strategies[args.strategy].__name__
    res["seed"] = args.seed
    print(json.dumps(res))
    if 'decrease' in res:
        if (res['decrease']):
            print("Termination was proven.")
            print('YES')
        else:
            print("Termination could not be proven.")
            print('MAYBE')
    else:
        print("Termination could not be proven.")
        print('MAYBE')


if __name__ == '__main__':

    # CHANGE THIS TO CHANGE DEFAULT SET TO RUN

    # =======================================
    # - parse arguments
    # =======================================
    parser = argparse.ArgumentParser()
    # parser.add_argument('--seed', dest='seed', type=int, default=199)
    parser.add_argument('--vcd-prefix', dest='vcd_prefix', help='Prefix of input VCD files')
    parser.add_argument('verilog', nargs='+', help='Input (System) Verilog files')
    parser.add_argument('--strategy', dest='strategy', help='Strategy to use for analysis.', required=True)
    parser.add_argument('--seed', dest='seed', help='Seed', type=int, required=False)
    parser.add_argument('--stratargs', dest='strat_args', type=str, help='Special arguments for strategies. Careful, this is strategy dependent.', required=False)


    args = parser.parse_args()

    main(args)


    #run_experiments(aprove_09_programs)
