# ----------------------------------------------------
# SPDX-FileCopyrightText: AsFigo Technologies, UK
# SPDX-FileCopyrightText: VerifWorks, India
# SPDX-License-Identifier: MIT
# Author: Himank Gangwal, Sep 02, 2025
# ----------------------------------------------------

from af_lint_rule import AsFigoLintRule
import logging
import anytree

class AssertPrefixCheck(AsFigoLintRule):
    """Checks if assert doesn't start with "a_" """

    def __init__(self, linter):
        self.linter = linter
        self.ruleID = "ASSERT_START_WITH_A"

    def apply(self, filePath: str, data: AsFigoLintRule.VeribleSyntax.SyntaxData):
        for curNode in data.tree.iter_find_all({"tag": "kAssertionItem"}):
            assert_name = self.getAssertPropertyName(curNode)
            if assert_name and not assert_name.startswith("a_"):
                message = (
                    f"Debug: Found assert name without a_ prefix. Use a_ as assert prefix\n"
                    f"Severely impacts verification completeness as errors may go undetected\n"
                    f"Assert property: {assert_name}\n"
                )
                self.linter.logViolation(self.ruleID, message)
        
    def getAssertPropertyName(self, assert_node):
        """Extracts the assert property name from an assert property statement."""
        # Look for SymbolIdentifier nodes that represent the assert property name
        for identifier in assert_node.iter_find_all({"tag": "SymbolIdentifier"}):
            # The first SymbolIdentifier in an assert property is usually the name
            return identifier.text
        return "Unknown"