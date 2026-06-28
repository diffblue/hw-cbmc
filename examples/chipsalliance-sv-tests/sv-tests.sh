#!/bin/sh

# abort on error
set -e

SCRIPT_DIR=$(cd "$(dirname "$0")" && pwd)

# clone sv-tests repo if not done yet
if [ ! -e sv-tests/.git ] ; then
  git clone https://github.com/chipsalliance/sv-tests
  (cd sv-tests && git checkout cbe02cf550b1345f5b75fee0c85145b1b68f379e)
fi

# install Python dependencies needed by the runner and report generator
pip3 install psutil pygments jinja2 markupsafe

# copy the ebmc runner
cp "$SCRIPT_DIR/ebmc.py" sv-tests/tools/runners/

cd sv-tests

# run the sv-tests and generate the HTML report
make report

# print a summary of pass/fail results
python3 - <<'EOF'
import os, sys

logs_dir = 'out/logs/ebmc'
if not os.path.exists(logs_dir):
    print("No test results found")
    sys.exit(0)

passed = []
failed = []

for fn in sorted(os.listdir(logs_dir)):
    path = os.path.join(logs_dir, fn)
    if not os.path.getsize(path):
        continue  # skipped test

    params = {}
    with open(path) as f:
        for line in f:
            line = line.rstrip()
            if not line:
                break
            key, _, val = line.partition(': ')
            params[key] = val

    tool_success = params.get('tool_success') == '1'
    should_fail = params.get('should_fail') == '1'
    tool_crashed = int(params.get('rc', 0)) >= 126

    test_passed = not tool_crashed and (should_fail != tool_success)

    name = params.get('name', fn)
    if test_passed:
        passed.append(name)
    else:
        failed.append(name)

for name in failed:
    print(f'FAIL: {name}')

total = len(passed) + len(failed)
print(f'\nebmc: {len(passed)} passed, {len(failed)} failed out of {total} tests')
EOF
