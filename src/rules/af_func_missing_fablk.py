# ----------------------------------------------------
# SPDX-FileCopyrightText: AsFigo Technologies, UK
# SPDX-FileCopyrightText: VerifWorks, India
# SPDX-License-Identifier: MIT
# ----------------------------------------------------
from af_lint_rule import AsFigoLintRule
import logging
import anytree

class FuncMissingFABLK(AsFigoLintRule):
    """Action block related checks """
  
    def __init__(self, linter):
        self.linter = linter  # Store the linter instance
        self.ruleID = "FUNC_MISSING_FAIL_ABLK"

    def apply(self, filePath: str, data: AsFigoLintRule.VeribleSyntax.SyntaxData):

        for curNode in data.tree.iter_find_all({"tag": "kAssertionItem"}):
            lvSvaCode = curNode.text

            lvAsrtFailAblkNode = curNode.iter_find_all({"tag": "kElseClause"})
            lvAsrtFailAblkNodeNxt = next(lvAsrtFailAblkNode, None)
            if lvAsrtFailAblkNodeNxt is None:
                message = (
                    f"FUNC: Missing fail action block in assert statement.\n"
                    f"Severly impacts verification completeness as errors may go undetected\n"
                    f"{lvSvaCode}\n"
                )
                self.linter.logViolation(self.ruleID, message)

