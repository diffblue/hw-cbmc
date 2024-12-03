#!/bin/sh

# abort on error
set -e

# clone Hazard3 repo if not done yet
if [ ! -e Hazard3/.git ] ; then
  git clone https://github.com/Wren6991/Hazard3 --branch v1.0 --depth 1
fi

cd Hazard3

vlindex -I hdl | tee vlindex-output

grep "Number of" vlindex-output > vlindex-output-filtered

# This errors when there's a diff
diff vlindex-output-filtered - << EOM
Number of files...........: 46
Number of symlinked files.: 0
Number of lines...........: 12093
Number of modules.........: 46
Number of UDPs............: 0
Number of checkers........: 0
Number of classes.........: 0
Number of packages........: 0
Number of interfaces......: 0
Number of functions.......: 7
Number of tasks...........: 0
Number of properties......: 0
Number of sequences.......: 0
Number of module instances: 71
Number of configurations..: 0
EOM
