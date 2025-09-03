# ----------------------------------------------------
# SPDX-FileCopyrightText: AsFigo Technologies, UK
# SPDX-FileCopyrightText: VerifWorks, India
# SPDX-License-Identifier: MIT
# Author: Himank Gangwal, Sep 02, 2025
# ----------------------------------------------------

from af_lint_rule import AsFigoLintRule
import logging
import anytree

class AssertNaming(AsFigoLintRule):
    """Checks if assert follows a naming convention - start with "a_" """

    def __init__(self, linter):
        self.linter = linter
        self.ruleID = "ASSERT_NAMING"

    def apply(self, filePath: str, data: AsFigoLintRule.VeribleSyntax.SyntaxData):
        for curNode in data.tree.iter_find_all({"tag": "kAssertionItem"}):
            assert_name = self.getAssertPropertyName(curNode)
            if assert_name and not assert_name.startswith("a_"):
                message = (
                    f"Debug: Found assert name without a_ prefix. "
                    f"Use a_ as assert prefix. This helps users to "
                    f"look for specific patterns in their log files. "
                    f"Found an Assertion as:\n"
                    f"{curNode.text}\n"
                )
                self.linter.logViolation(self.ruleID, message, "WARNING")
        
    def getAssertPropertyName(self, assert_node):
        """Extracts the assert property name from an assert property statement."""
        # Look for SymbolIdentifier nodes that represent the assert property name
        for identifier in assert_node.iter_find_all({"tag": "SymbolIdentifier"}):
            # The first SymbolIdentifier in an assert property is usually the name
            return identifier.text
        return "Unknown"
