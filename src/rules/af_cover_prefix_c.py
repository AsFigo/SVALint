# ----------------------------------------------------
# SPDX-FileCopyrightText: AsFigo Technologies, UK
# SPDX-FileCopyrightText: VerifWorks, India
# SPDX-License-Identifier: MIT
# Author: Himank Gangwal, June 07, 2025
# ----------------------------------------------------

from af_lint_rule import AsFigoLintRule
import logging
import anytree

class CoverPrefixCheck(AsFigoLintRule):
    """Checks if cover doesn't start with "c_" """

    def __init__(self, linter):
        self.linter = linter
        self.ruleID = "COVER_START_WITH_C"

    def apply(self, filePath: str, data: AsFigoLintRule.VeribleSyntax.SyntaxData):
        for curNode in data.tree.iter_find_all({"tag": "kCoverPoint"}):
            lvSvaCode = self.getHeaderName(curNode)
            if (lvSvaCode[0:2] != "c_"):
                message = (
                    f"Debug: Found cover name without c_ prefix. Use c_ as cover prefix\n"
                    f"{lvSvaCode}\n"
                )
                self.linter.logViolation(self.ruleID, message)
        
                
    def getHeaderName(self, header):
        """Extracts the class name from a class declaration."""
        for identifier in header.iter_find_all({"tag": "SymbolIdentifier"}):
            return identifier.text
        return "Unknown"