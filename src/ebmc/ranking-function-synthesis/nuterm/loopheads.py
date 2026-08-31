import os
import pathlib

def get_loop_heads(jar, klass, function):
    from jnius import autoclass

    # String = autoclass("java.lang.String")
    # calc_lh = autoclass('main.CalculateLoopHeads')

    # x = calc_lh.calculateLoopHeadsHelper(String(jar), String(klass), String(function))

    URL = autoclass('java.net.URL')
    URLClassLoader = autoclass('java.net.URLClassLoader')

    #print()
    #for x in os.environ['CLASSPATH'].split(":"):
    #    print(x)
    #print()
    CFGAnalyzer = autoclass('javachecker.CFGAnalyzer')

    urls = [URL('jar:file:' + jar + '!/')]
    cl = URLClassLoader.newInstance(urls)
    heads = CFGAnalyzer.loopHeaders(cl, klass, function)
    print("Done")

    return heads.toArray()


if __name__ == '__main__':
    from jnius import autoclass

    os.environ['CLASSPATH'] = str(pathlib.Path(__file__).parent.absolute()) + "../libs/CalculateLoopHeads.jar"

    String = autoclass("java.lang.String")
    calc_lh = autoclass('main.CalculateLoopHeads')

    exit(0)
    x = get_loop_heads("./examples/GCD/GCD.jar", "classes.GCD", "gcd")
    print(x)
