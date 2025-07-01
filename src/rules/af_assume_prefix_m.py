# ----------------------------------------------------
# SPDX-FileCopyrightText: AsFigo Technologies, UK
# SPDX-FileCopyrightText: VerifWorks, India
# SPDX-License-Identifier: MIT
# Author: Himank Gangwal, June 28, 2025
# ----------------------------------------------------

from af_lint_rule import AsFigoLintRule
import logging
import anytree

class AssumePrefixCheck(AsFigoLintRule):
    """Checks if assume doesn't start with "m_" """

    def __init__(self, linter):
        self.linter = linter
        self.ruleID = "ASSUME_START_WITH_M"

    def apply(self, filePath: str, data: AsFigoLintRule.VeribleSyntax.SyntaxData):
        for curNode in data.tree.iter_find_all({"tag": "kAssumePropertyStatement"}):
            lvSvaCode = self.getHeaderName(curNode)
            if (lvSvaCode[0:2] != "m_"):
                message = (
                    f"Debug: Found assume name without m_ prefix. Use m_ as assume prefix"
                    f"{lvSvaCode}\n"
                )

                self.linter.logViolation(self.ruleID, message)
                
    def getHeaderName(self, header):
        """Extracts the class name from a class declaration."""
        for identifier in header.iter_find_all({"tag": "SymbolIdentifier"}):
            return identifier.text
        return "Unknown"