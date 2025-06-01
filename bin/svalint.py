# ----------------------------------------------------
# SPDX-FileCopyrightText: AsFigo Technologies, UK
# SPDX-FileCopyrightText: VerifWorks, India
# SPDX-License-Identifier: MIT
# ----------------------------------------------------

import sys
import os
# Add the 'src' directory to the Python path
sys.path.append(os.path.abspath(os.path.join(os.path.dirname(__file__), '../src')))

import logging
import verible_verilog_syntax
from af_lint_rule import AsFigoLintRule
from asfigo_linter import AsFigoLinter
from rules.af_asrt_no_label import MissingLabelChk
from rules.af_perf_no_pass_ablk import PerfNoPABlk

class SVALinter(AsFigoLinter):
    """Linter that applies multiple rules on SVA code"""

    def __init__(self, configFile, logLevel=logging.INFO):
        super().__init__(configFile=configFile, logLevel=logLevel)
        # Automatically discover and register all subclasses of AsFigoLintRule
        self.rules = [rule_cls(self) for rule_cls in AsFigoLintRule.__subclasses__()]

    def loadSyntaxTree(self):
        """Loads Verilog syntax tree using VeribleVerilogSyntax."""
        parser = verible_verilog_syntax.VeribleVerilogSyntax()
        return parser.parse_files([self.testName], options={"gen_tree": True})

    def runLinter(self):
        """Runs all registered lint rules on the Verilog file."""
        treeData = self.loadSyntaxTree()

        for filePath, fileData in treeData.items():
            self.logInfo("SVALint", f"Loaded test file: {self.testName}")
            
            for rule in self.rules:
                rule.run(filePath, fileData)

            self.logSummary()


if __name__ == "__main__":
    byolDemo = SVALinter(configFile="config.toml", logLevel=logging.INFO)
    byolDemo.runLinter()
