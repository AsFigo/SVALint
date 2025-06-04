# ----------------------------------------------------
# SPDX-FileCopyrightText: AsFigo Technologies, UK
# SPDX-FileCopyrightText: VerifWorks, India
# SPDX-License-Identifier: MIT
# ----------------------------------------------------

from af_lint_rule import AsFigoLintRule
import logging
import anytree


class NoWithinOperInAsrt(AsFigoLintRule):
    """
    From book: https://payhip.com/b/7HvMk
    by @hdlcohen
    Avoid within operator in SVA
    Note: The within is a sequence operator. It is introduced
    here due to its popularity; however, its usage can be
    misleading. For reasons explained below, I recommend
    avoiding the within operator.
    """

    def __init__(self, linter):
        self.linter = linter
        # Store the linter instance
        self.ruleID = "STYLE_AVOID_WITHIN_A"

    def apply(self, filePath: str, data: AsFigoLintRule.VeribleSyntax.SyntaxData):
        lvMsg = (
            f"From book: https://payhip.com/b/7HvMk\n"
            f"by @hdlcohen\n"
            f"Avoid within operator in SVA\n"
            f"Note: The within is a sequence operator. It is introduced\n"
            f"here due to its popularity; however, its usage can be \n"
            f"misleading. For reasons explained below, I recommend \n"
            f"avoiding the within operator."
        )

        for curNode in data.tree.iter_find_all({"tag": "kAssertionItem"}):
            lvSvaCode = curNode.text
            lvWithinG = curNode.iter_find_all({"tag": "within"})
            lvWithinList = list(lvWithinG)
            if len(lvWithinList) > 0:
                message = f"{lvMsg}\n" f"{lvSvaCode}\n"

                self.linter.logViolation(self.ruleID, message)
