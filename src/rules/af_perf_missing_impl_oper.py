# ----------------------------------------------------
# # SPDX-FileCopyrightText: AsFigo Technologies, UK
# # SPDX-FileCopyrightText: VerifWorks, India
# # SPDX-License-Identifier: MIT
# # ----------------------------------------------------
from af_lint_rule import AsFigoLintRule
import logging
import anytree


class MissingImplicationOper(AsFigoLintRule):
    cfgMsg = """    SVA properties without implication operators  
          are generally poor for simulation performance    
            (unless codes in forbid property style, not so commonly used).   
              """

    def __init__(self, linter):
        self.linter = linter  # Store the linter instance
        self.ruleID = "PERF_MISSING_IMPLICATION_OPER"

    def apply(self, filePath: str, data: AsFigoLintRule.VeribleSyntax.SyntaxData):
        for curNode in data.tree.iter_find_all({"tag": "kPropertyDeclaration"}):
            lvSvaCode = curNode.text
            lvOlapImplG = curNode.iter_find_all({"tag": "|->"})
            lvNonOlapImplG = curNode.iter_find_all({"tag": "|=>"})
            lvNumImplOper = len(list(lvOlapImplG)) + len(list(lvNonOlapImplG))
            if lvNumImplOper == 0:
                message = f"{self.cfgMsg}\n" f"{lvSvaCode}\n"
                self.linter.logViolation(self.ruleID, message)
