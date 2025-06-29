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
from rules.af_no_timeliteral import NoExplTimeLiterals
from rules.af_no_within_oper import NoWithinOperInAsrt
from rules.af_no_fmatch_oper import NoFirstMatchOperInAsrt
from rules.af_no_range_ant import NoRangeInAntAsrt
from rules.af_perf_no_ub_range_ant import NoUBRangeInAntAsrt
from rules.af_func_missing_fablk import FuncMissingFABLK
from rules.af_missing_elbl_prop import MissingEndLblProp
from rules.af_missing_elbl_seq import MissingEndLblSEQ
from rules.af_perf_missing_impl_oper import MissingImplicationOper
from rules.af_perf_no_large_del import NoLargeDelayProp

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
