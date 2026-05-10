

#  READ THIS BEFORE REMOVING !!!!!!!!
# PLEASE LEAVE THIS THE WAY IT IS. If you remove this my workflow and everything get's destroyed. It is maybe not
# nicest solution but it work for the time being. If you remove this one has to work from the terminal and export
# all paths, which I do not think is a nice solution either, as I am not working from the terminal but the IDE.
# PLEASE leave this until we have a nice and robust solution.
import pathlib
import os

from loopheads import get_loop_heads

file_path = str(pathlib.Path(__file__).parent.absolute())
# os.environ['CLASSPATH'] = ':'.join([e.path for e in os.scandir(file_path + '/../libs/')])
from jnius import autoclass, cast

import numpy as np


def check(jar_name, class_name, method_name, offset, ranking_args, ranking_fun):
    #for x in os.environ['CLASSPATH']:
    #    print(x)
    #exit(0)
    RankChecker = autoclass('javachecker.RankChecker')
    
    URL = autoclass('java.net.URL')
    URLClassLoader = autoclass('java.net.URLClassLoader')
    List = autoclass('java.util.List')
    
    urls = [URL('jar:file:' + jar_name + '!/')]
    cl = cast("java.lang.ClassLoader", URLClassLoader.newInstance(urls))
    #cl = URLClassLoader.newInstance(urls)
    
    args = List.of(*ranking_args)
    fun = List.of(*ranking_fun)
    
    res = RankChecker._check(cl, class_name, method_name, offset, args, fun)
    
    return bool(res[0]), bool(res[1])


def last_line_offset(jar_name, class_name, method_name, line):

    URL = autoclass('java.net.URL')
    URLClassLoader = autoclass('java.net.URLClassLoader')

    CFGAnalyzer = autoclass('javachecker.CFGAnalyzer')

    urls = [URL('jar:file:' + jar_name + '!/')]
    cl = URLClassLoader.newInstance(urls)

    line_to_offset = CFGAnalyzer.lineToLabelOffset(cl, class_name, method_name)
    return line_to_offset.get(line).last()

def check_sum_of_relu(jar_name, class_name, method_name, ranking_heads,
                      ranking_args, ranking_out, ranking_W, ranking_b):

    #for x in os.environ['LD_LIBRARY_PATH'].split(":"):
    #    print(x)
    RankChecker = autoclass('javachecker.RankChecker')
    
    URL = autoclass('java.net.URL')
    URLClassLoader = autoclass('java.net.URLClassLoader')
    List = autoclass('java.util.List')
    HashMap = autoclass('java.util.HashMap')

    urls = [URL('jar:file:' + jar_name + '!/')]
    cl = cast("java.lang.ClassLoader", URLClassLoader.newInstance(urls))
    #cl = URLClassLoader.newInstance(urls)

    #print(ranking_W)
    #print(ranking_b)
    #print(ranking_out)

    assert len(ranking_W) == len(ranking_heads)
    assert len(ranking_b) == len(ranking_heads)
    assert len(ranking_out) == len(ranking_heads)
    fun = []
    for W,b in zip(ranking_W, ranking_b):

        assert np.shape(W)[0] == np.shape(b)[0]
        SOR = []
        for i in range(0, np.shape(W)[0]):
            SOR.append([int(x) for x in W[i,:]] + [int(b[i])])
        fun.append(SOR)

    args = List.of(*ranking_args)
    heads = List.of(*ranking_heads)
    out = List.of(*[List.of(*[int(x) for x in W[0,:]]) for W in ranking_out])
    hidden = List.of(*[List.of(*[List.of(*row) for row in relus]) for relus in fun])
    cex = HashMap()

    res = RankChecker._checkLexiReluOrCex2(cl, class_name, method_name, heads, args, out, hidden, cex)

    cexDict = {}
    i = cex.entrySet().iterator()
    while i.hasNext():
      e = i.next()
      (k,v) = e.getKey(),e.getValue()
      cexDict[k] = v

    return bool(res[0]), bool(res[2]), cexDict
    
if __name__ == '__main__':

    jarfile = "../benchmarking/termination-suite/termination-crafted-lit/terminating/NoriSharmaFSE2013Fig7/NoriSharmaFSE2013Fig7.jar"
    classname = "NoriSharmaFSE2013Fig7"
    methodname = "loop"
    input_vars = ['i', 'j', 'M', 'N', 'a', 'b', 'c']

    loop_heads = get_loop_heads(jarfile, classname, methodname)

    W_to_check = [np.array([[-1.,  0., -2.,  2.,  1.,  0., -0.],
                           [-0., -2.,  2., -2.,  3.,  0., -0.],
                           [ 0., 0.,  0.,  0.,  0., 0., 0.],
                           [-2.,  1.,  3., -0., -2.,  0., -0.],
                           [-1., -1., -0.,  2., -2., 0.,  0.]])]
    b_to_check = [np.array([1., 1., 2., 3., 3.])]
    out_to_check = [np.array([[1., 1., 0., 1., 1.]])]



    decrease, invar, cex = check_sum_of_relu(jarfile, classname, methodname,
                                                           loop_heads, input_vars,
                                                           out_to_check, W_to_check, b_to_check)

    print("Decreasing: {}".format(decrease))
    print("Invar: {}".format(invar))
    print("Cex: {}".format(cex))
