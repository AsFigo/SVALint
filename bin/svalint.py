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
from rules.af_prop_naming import PropNaming
from rules.af_perf_missing_impl_oper import MissingImplicationOper
from rules.af_perf_no_large_del import NoLargeDelayProp
from rules.af_use_simple_cnseq import UseSimpleExprConseq
from rules.af_no_dollar_time import UseRealTimeVsTime
from rules.af_func_cov_nolap import FuncNOLAPInCoverProp 
from rules.af_func_cov_olap import FuncOLAPInCoverProp 
from rules.af_reuse_fa_one_liner import ReuseNoOneLinerFABLK 
from rules.af_func_no_ub_in_cnseq import NoUBRangeInConseqAsrt 
from rules.af_asrt_naming import AssertNaming
from rules.af_no_aa_exists_sva import AvoidAAExistsSVA
from rules.af_no_pop_back_sva import AvoidPopBkSVA
from rules.af_no_pop_front_sva import AvoidPopFrSVA
from rules.af_assume_naming import AssumeNaming
from rules.af_cover_naming import CoverNaming

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
