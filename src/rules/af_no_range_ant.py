# ----------------------------------------------------
# SPDX-FileCopyrightText: AsFigo Technologies, UK
# SPDX-FileCopyrightText: VerifWorks, India
# SPDX-License-Identifier: MIT
# ----------------------------------------------------

from af_lint_rule import AsFigoLintRule
import logging
import anytree


class NoRangeInAntAsrt(AsFigoLintRule):
    lvMsg = """
    From book: https://payhip.com/b/7HvMk
    by @hdlcohen
    Avoid ranges in antecedent.
    Design sequences so that if a match occurs, it excludes all other
potential matches. This ensures that only one valid sequence is considered.
2.2.2.2 Sequence Writing Styles
The goal is to write a sequence that excludes all other potential matches once a match occurs.
SystemVerilog's goto and non-consecutive operators facilitate this. The goto repetition operator
[->n] allows a Boolean expression to repeat until it becomes true, enabling non-consecutive occurrences.
The goto operator expr[->1] searches over multiple cycles for the first sequence where expr becomes true,
after previous threads were false (see Section 3.4).

// Example: rdy[->1] is equivalent to:
// (rdy) or (!rdy ##1 rdy) or
// (!rdy ##1 !rdy ##1 rdy) or (!rdy ##1 !rdy ##1 !rdy ... ##1 rdy)
// Once rdy==1, there cannot be another thread with rdy==1
// Application example:
// Instead of: 
ap_avoid: assert property(@ (posedge clk)
   $rose(req) ##[1:10] rdy |-> ##[1:2] ack );
// Use: 
ap_better: assert property(@ (posedge clk)
   $rose(req) ##1 rdy[->1] |-> ##[1:2] ack); // only one possible match in the antecedent.
// All ORed threads where rdy==0 create vacuous assertions for these threads.
// The ONLY thread that creates a nonvacuous assertion is the one and only one when rdy=1.
    """

    def __init__(self, linter):
        self.linter = linter
        # Store the linter instance
        self.ruleID = "STYLE_AVOID_RANGE_IN_ANT_A"

    def apply(self, filePath: str, data: AsFigoLintRule.VeribleSyntax.SyntaxData):

        for curNode in data.tree.iter_find_all({"tag": "kAssertionItem"}):
            lvSvaCode = curNode.text
            lvImplG = curNode.iter_find_all({"tag": "kPropertyImplicationList"})
            for curImplNode in curNode.iter_find_all({"tag": "kPropertyImplicationList"}):
                lvImplAntNode = curImplNode.children[0]
                lvAntRangeG = lvImplAntNode.iter_find_all({"tag": "kCycleRange"})
                lvAntRangeList = list(lvAntRangeG)
                if len(lvAntRangeList) > 0:
                    message = f"{self.lvMsg}\n" f"{lvSvaCode}\n"

                    self.linter.logViolation(self.ruleID, message)
