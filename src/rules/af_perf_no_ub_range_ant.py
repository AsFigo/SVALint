# ----------------------------------------------------
# SPDX-FileCopyrightText: AsFigo Technologies, UK
# SPDX-FileCopyrightText: VerifWorks, India
# SPDX-License-Identifier: MIT
# ----------------------------------------------------

from af_lint_rule import AsFigoLintRule
import logging
import anytree


class NoUBRangeInAntAsrt(AsFigoLintRule):
    lvMsg = """
    From book: https://payhip.com/b/7HvMk

by @hdlcohen

Limiting Potential Matches: Restrict the number of possible matches to prevent state space
explosion. This can be done by using fixed delays or bounded ranges instead of unbounded ones
(e.g., ##[1:5] instead of ##[1:$] ).
The general recommendation is to avoid using infinite or large ranges in SystemVerilog assertions by
bounding them to reasonable values for the design. This recommendation is particularly true for formal
verification. For example, instead of using ##[1:$], which represents a range from 1 to infinity, it’s
better to use a finite range like ##[1:10], or to rethink the structure of the assertions. In practice, if the
design allows for a response within a range of cycles and this flexibility is intended, using something like
##[1:10] is acceptable and can be more representative of the actual behavior. However, if the design is
expected to respond in a fixed number of cycles, or if you're facing performance issues with the formal
tool, consider using a more deterministic delay

    """

    def __init__(self, linter):
        self.linter = linter
        # Store the linter instance
        self.ruleID = "PERF_AVOID_$_RANGE_IN_ANT_A"

    def apply(self, filePath: str, data: AsFigoLintRule.VeribleSyntax.SyntaxData):

        for curNode in data.tree.iter_find_all({"tag": "kAssertionItem"}):
            lvSvaCode = curNode.text
            lvImplG = curNode.iter_find_all({"tag": "kPropertyImplicationList"})
            for curImplNode in curNode.iter_find_all({"tag": "kPropertyImplicationList"}):
                lvImplAntNode = curImplNode.children[0]
                lvAntRangeG = lvImplAntNode.iter_find_all({"tag": "kCycleDelayRange"})
                for curDelRangeNode in lvAntRangeG:
                    lvAntUBRangeG = curDelRangeNode.iter_find_all({"tag": "$"})
                    lvAntUBRangeList = list(lvAntUBRangeG)
                    if len(lvAntUBRangeList) > 0:
                        message = f"{self.lvMsg}\n" f"{lvSvaCode}\n"

                        self.linter.logViolation(self.ruleID, message)
