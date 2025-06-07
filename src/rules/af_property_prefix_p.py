# ----------------------------------------------------
# SPDX-FileCopyrightText: AsFigo Technologies, UK
# SPDX-FileCopyrightText: VerifWorks, India
# SPDX-License-Identifier: MIT
# Author: Himank Gangwal, June 07, 2025
# ----------------------------------------------------

from af_lint_rule import AsFigoLintRule
import logging
import anytree

class PropertyPrefixCheck(AsFigoLintRule):
    """Checks if property doesn't start with "p_" """

    def __init__(self, linter):
        self.linter = linter
        self.ruleID = "PROP_START_WITH_P"

    def apply(self, filePath: str, data: AsFigoLintRule.VeribleSyntax.SyntaxData):
        for curNode in data.tree.iter_find_all({"tag": "kPropertyDeclaration"}):
            lvSvaCode = self.getHeaderName(curNode)
            if (lvSvaCode[0:2] != "p_"):
                message = (
                    f"Debug: Found property name without p_ prefix. Use p_ as property prefix\n"
                    f"Severly impacts verification completeness as errors may go undetected\n"
                    f"{lvSvaCode}\n"
                )

                self.linter.logViolation(self.ruleID, message)
                
    def getHeaderName(self, header):
        """Extracts the class name from a class declaration."""
        for identifier in header.iter_find_all({"tag": "SymbolIdentifier"}):
            return identifier.text
        return "Unknown"