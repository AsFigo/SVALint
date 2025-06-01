# ----------------------------------------------------
# SPDX-FileCopyrightText: AsFigo Technologies, UK
# SPDX-FileCopyrightText: VerifWorks, India
# SPDX-License-Identifier: MIT
# ----------------------------------------------------
from af_lint_rule import AsFigoLintRule
import logging
import anytree

class PerfNoPABlk(AsFigoLintRule):
    """Action block related checks """
  
    def __init__(self, linter):
        self.linter = linter  # Store the linter instance
        self.ruleID = "PERF_PASS_ACT_BLK"

    def apply(self, filePath: str, data: AsFigoLintRule.VeribleSyntax.SyntaxData):

        for curNode in data.tree.iter_find_all({"tag": "kAssertionItem"}):
            lvSvaCode = curNode.text

            lvAsrtPassAblkNode = curNode.iter_find_all({"tag": "kAssertPropertyBody"})
            lvAsrtPassAblkNodeNxt = next(lvAsrtPassAblkNode)
            lvNullNode = lvAsrtPassAblkNodeNxt.iter_find_all({"tag": "kNullStatement"})
            lvNullNodeList = list(lvNullNode)


            if (len(lvAsrtPassAblkNodeNxt.text) > 1):
                message = (
                    f"PERF: Found a pass-action-block in assert statement.\n"
                    f"Severly impacts performance in simulation, avoid pass action blocks!\n"
                    f"{lvSvaCode}\n"
                )
                self.linter.logViolation(self.ruleID, message)

