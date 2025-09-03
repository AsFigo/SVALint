# ----------------------------------------------------
# SPDX-FileCopyrightText: AsFigo Technologies, UK
# SPDX-FileCopyrightText: VerifWorks, India
# SPDX-License-Identifier: MIT
# ----------------------------------------------------

from af_lint_rule import AsFigoLintRule
import logging
import anytree


class NoUBRangeInConseqAsrt(AsFigoLintRule):
    lvMsg = """
    From book: https://payhip.com/b/7HvMk

by @hdlcohen

An assertion with an infinite range in its consequent can never FAIL, but can PASS.

$rose(req) |-> ##[0:$] ack);
Consider using a more deterministic delay

    """

    def __init__(self, linter):
        self.linter = linter
        # Store the linter instance
        self.ruleID = "FUNC_AVOID_$_RANGE_IN_CONSEQ_A"

    def apply(self, filePath: str, data: AsFigoLintRule.VeribleSyntax.SyntaxData):

        for curNode in data.tree.iter_find_all({"tag": "kAssertionItem"}):
            lvSvaCode = curNode.text
            for curImplNode in curNode.iter_find_all({"tag": "|->"}):
                print (anytree.RenderTree(curImplNode))
                print (curImplNode)
                print (dir(curImplNode))
                print (curImplNode.siblings)
                print (type(curImplNode.siblings))
                lvImplCnseqNode = curImplNode.siblings[1]
                lvRangeG = lvImplCnseqNode.iter_find_all({"tag": "kCycleDelayRange"})
                for curDelRangeNode in lvRangeG:
                    lvCnseqUBRangeG = curDelRangeNode.iter_find_all({"tag": "$"})
                    lvCnseqUBRangeList = list(lvCnseqUBRangeG)
                    if len(lvCnseqUBRangeList) > 0:
                        message = f"{self.lvMsg}\n" f"{lvSvaCode}\n"

                        self.linter.logViolation(self.ruleID, message)
