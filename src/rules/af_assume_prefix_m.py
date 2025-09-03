# ----------------------------------------------------
# SPDX-FileCopyrightText: AsFigo Technologies, UK
# SPDX-FileCopyrightText: VerifWorks, India
# SPDX-License-Identifier: MIT
# Author: Himank Gangwal, Sep 02, 2025
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
            assume_name = self.getAssumePropertyName(curNode)
            if assume_name and not assume_name.startswith("m_"):
                message = (
                    f"Debug: Found assume name without m_ prefix. Use m_ as assume prefix\n"
                    f"Assume property: {assume_name}\n"
                )
                self.linter.logViolation(self.ruleID, message)
                
    def getAssumePropertyName(self, assume_node):
        """Extracts the assume property name from an assume property statement."""
        # Look for SymbolIdentifier nodes that represent the assume property name
        for identifier in assume_node.iter_find_all({"tag": "SymbolIdentifier"}):
            # The first SymbolIdentifier in an assume property is usually the name
            return identifier.text
        return "Unknown"