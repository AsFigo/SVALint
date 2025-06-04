# ----------------------------------------------------
# SPDX-FileCopyrightText: AsFigo Technologies, UK
# SPDX-FileCopyrightText: VerifWorks, India
# SPDX-License-Identifier: MIT
# ----------------------------------------------------

from af_lint_rule import AsFigoLintRule
import logging
import anytree


class MissingEndLblProp(AsFigoLintRule):
    """Checks for missing end-labels in property """

    def __init__(self, linter):
        self.linter = linter
        # Store the linter instance
        self.ruleID = "DBG_MISS_END_LBL_PROP"

    def apply(
        self, filePath: str, data: AsFigoLintRule.VeribleSyntax.SyntaxData
    ):
        for curNode in data.tree.iter_find_all(
            {"tag": "kPropertyDeclaration"}):
            lvSvaCode = curNode.text
            lvLastElem = curNode.descendants[-1]
            if (not lvLastElem.text):
                message = (
                    f"Debug: Found a property without endlabel. Use of endlabels "
                    f"greatly enhances debug and increases productivity\n"
                    f"{lvSvaCode}\n"
                )

                self.linter.logViolation(self.ruleID, message)
