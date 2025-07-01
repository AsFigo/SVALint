# ----------------------------------------------------
# # SPDX-FileCopyrightText: AsFigo Technologies, UK
# # SPDX-FileCopyrightText: VerifWorks, India
# # SPDX-License-Identifier: MIT
#
# # ----------------------------------------------------
from af_lint_rule import AsFigoLintRule
import logging
import anytree


class NoLargeDelayProp(AsFigoLintRule):
    cfgMsg = """    Avoid large delays in SVA.    
    Using large delays in number of clocks inside SVA     
    property expressions may lead to simulation performance  issues. 
    By default SVALint checks cfgMaxDelay as 100
    """

    def __init__(self, linter):
        self.linter = linter  # Store the linter instance
        self.ruleID = "PERF_NO_LARGE_DELAY"
        self.cfgMaxDelay = 100

    def apply(self, filePath: str, data: AsFigoLintRule.VeribleSyntax.SyntaxData):
        for curNode in data.tree.iter_find_all({"tag": "kPropertyDeclaration"}):
            lvSvaCode = curNode.text
            lvDelayG = curNode.iter_find_all({"tag": "kCycleDelayRange"})
            for curDelNode in lvDelayG:
                lvDelValG = curDelNode.iter_find_all({"tag": "TK_DecNumber"})
                for curDelValNode in lvDelValG:
                    if int(curDelValNode.text) > self.cfgMaxDelay:
                        message = f"{self.cfgMsg}\n" f"{lvSvaCode}\n"
                        self.linter.logViolation(self.ruleID, message)
