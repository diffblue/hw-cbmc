#!/usr/bin/env python3
# -*- coding: utf-8 -*-

from BaseRunner import BaseRunner
import os

class ebmc(BaseRunner):
    def __init__(self):
        super().__init__(
            'ebmc', 'ebmc', {
                'preprocessing', 'parsing', 'elaboration'
            })

        self.submodule = "third_party/tools/ebmc"
        self.url = f"https://github.com/diffblue/hw-cbmc/tree/{self.get_commit()}"

    def prepare_run_cb(self, tmp_dir, params):
        ofile = 'ebmc.out'

        self.cmd = [self.executable]

        if params['mode'] == 'preprocessing':
            self.cmd.append('--preprocess')
        elif params['mode'] == 'parsing':
            self.cmd += ['--show-parse']

        if params['top_module'] != '':
            self.cmd += ['--module', params['top_module']]

        for incdir in params['incdirs']:
            self.cmd.append('-I' + incdir)

        for define in params['defines']:
            self.cmd.append('-D' + define)

        self.cmd += params['files']

    def get_version_cmd(self):
        return [self.executable, "--version"]

    def get_version(self):
        version = super().get_version()

        # The full version is the 1st line
        version = version.splitlines()[0]

        version.insert(0, self.name)

        return " ".join(version)
