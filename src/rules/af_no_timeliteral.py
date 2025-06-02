# ----------------------------------------------------
# SPDX-FileCopyrightText: AsFigo Technologies, UK
# SPDX-FileCopyrightText: VerifWorks, India
# SPDX-License-Identifier: MIT
# ----------------------------------------------------

from af_lint_rule import AsFigoLintRule
import logging
import anytree


class NoExplTimeLiterals(AsFigoLintRule):
    """Avoid explicit time literals in SVA"""

    def __init__(self, linter):
        self.linter = linter
        # Store the linter instance
        self.ruleID = "REUSE_NO_TIMELITERAL"

    def apply(
        self, filePath: str, data: AsFigoLintRule.VeribleSyntax.SyntaxData
    ):
        for curNode in data.tree.iter_find_all(
            {"tag": "kPropertyDeclaration"}
        ):
            lvSvaCode = curNode.text
            lvTimeLiteralG = curNode.iter_find_all({"tag": "TK_TimeLiteral"})
            lvTimeLiteralList = list(lvTimeLiteralG)
            if len(lvTimeLiteralList) > 0:
                message = (
                    f"REUSE: Found an Explicit Time Literal in a property "
                    f"declaration. Avoid explicit values, use parameters or "
                    f"`define-s instead\n"
                    f"{lvSvaCode}\n"
                )

                self.linter.logViolation(self.ruleID, message)
