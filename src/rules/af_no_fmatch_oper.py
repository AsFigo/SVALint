# ----------------------------------------------------
# SPDX-FileCopyrightText: AsFigo Technologies, UK
# SPDX-FileCopyrightText: VerifWorks, India
# SPDX-License-Identifier: MIT
# ----------------------------------------------------

from af_lint_rule import AsFigoLintRule
import logging
import anytree


class NoFirstMatchOperInAsrt(AsFigoLintRule):
    lvMsg = """
    From book: https://payhip.com/b/7HvMk
    by @hdlcohen
    NOTE: Experts often discourage using first_match() in formal verification; it is acceptable in simulation.
The first_match() function in SVA can be problematic for formal verification for several reasons:

Performance Impact
The first_match() creates multiple concurrent threads that the tool must evaluate, potentially
leading to state-space explosion.
Complexity
The first_match() adds complexity to assertions, making them more difficult to understand and
maintain. This complexity can obscure the intent of the assertion and make debugging more
challenging.
By avoiding and opting for clearer, more direct assertions, you can improve the effectiveness of formal
verification efforts and make your assertions more robust and maintainable.
    """

    def __init__(self, linter):
        self.linter = linter
        # Store the linter instance
        self.ruleID = "STYLE_AVOID_FIRST_MATCH_A"

    def apply(self, filePath: str, data: AsFigoLintRule.VeribleSyntax.SyntaxData):

        for curNode in data.tree.iter_find_all({"tag": "kAssertionItem"}):
            lvSvaCode = curNode.text
            lvFirstMatchG = curNode.iter_find_all({"tag": "first_match"})
            lvFirstMatchList = list(lvFirstMatchG)
            if len(lvFirstMatchList) > 0:
                message = f"{self.lvMsg}\n" f"{lvSvaCode}\n"

                self.linter.logViolation(self.ruleID, message)
