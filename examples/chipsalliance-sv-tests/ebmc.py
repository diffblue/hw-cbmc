#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""ebmc runner for chipsalliance/sv-tests.

This plugs EBMC into the sv-tests test harness
(https://github.com/chipsalliance/sv-tests).  sv-tests auto-discovers
runners: every *.py file placed under tools/runners/ is imported, and,
provided ebmc.can_run() (inherited from BaseRunner; checks that the
'ebmc' executable is on $PATH) succeeds, used to run the test cases
under tests/.  See sv-tests.sh in this directory, which copies this
file into a checkout of sv-tests before invoking 'make report'; no
further registration is required.

Only EBMC's front end is exercised here (--preprocess / --show-parse),
since sv-tests measures parsing/elaboration coverage rather than
verification results, so most of BaseRunner's simulation-related hooks
are unused.

Unlike the other runners under tools/runners/, EBMC is not vendored into
sv-tests as a git submodule, so BaseRunner.get_commit() (which looks up
the checked-out commit of a submodule) cannot report a meaningful
version; 'url' is therefore a static link to the hw-cbmc repository
rather than a link to a specific revision.

Requirements: the 'ebmc' binary must be on $PATH when the runner is
invoked.
"""

import os

from BaseRunner import BaseRunner

# sv-tests limits the runtime of each test (30 s by default), but not its
# memory. Some tests make EBMC allocate memory faster than the timeout
# can stop it, which exhausts the memory of the CI runner and takes down
# the entire job. Each invocation of EBMC is hence run with a limit on its
# address space, in KiB; set EBMC_MEMORY_LIMIT_KB to override.
MEMORY_LIMIT_KB = int(os.environ.get('EBMC_MEMORY_LIMIT_KB', 4 * 1024 * 1024))


class ebmc(BaseRunner):
    def __init__(self):
        super().__init__(
            'ebmc', 'ebmc', {
                'preprocessing', 'parsing', 'elaboration'
            })

        self.url = "https://github.com/diffblue/hw-cbmc"

    def prepare_run_cb(self, tmp_dir, params):
        self.cmd = [self.executable]

        if params['mode'] == 'preprocessing':
            self.cmd.append('--preprocess')
        elif params['mode'] == 'parsing':
            self.cmd += ['--show-parse']

        if params['top_module'] != '':
            self.cmd += ['--top', params['top_module']]

        for incdir in params['incdirs']:
            self.cmd.append('-I' + incdir)

        for define in params['defines']:
            self.cmd.append('-D' + define)

        self.cmd += params['files']

        # Apply the memory limit; 'exec' replaces the shell by EBMC, so
        # that the exit status and the timeout apply to EBMC itself.
        self.cmd = [
            'sh', '-c', 'ulimit -v %d && exec "$@"' % MEMORY_LIMIT_KB, 'sh'
        ] + self.cmd

    def get_version_cmd(self):
        return [self.executable, "--version"]

    def get_version(self):
        version = super().get_version()

        # The full version is the 1st line
        version = version.splitlines()[0].split()

        version.insert(0, self.name)

        return " ".join(version)
