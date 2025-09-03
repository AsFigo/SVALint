# ----------------------------------------------------
# SPDX-FileCopyrightText: AsFigo Technologies, UK
# SPDX-FileCopyrightText: VerifWorks, India
# SPDX-License-Identifier: MIT
# Author: Himank Gangwal, Sep 02, 2025
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
            # Look for the cover point name in the syntax tree
            cover_name = self.getCoverPointName(curNode)
            if cover_name and not cover_name.startswith("c_"):
                message = (
                    f"Debug: Found cover name without c_ prefix. Use c_ as cover prefix\n"
                    f"Cover point: {cover_name}\n"
                )
                self.linter.logViolation(self.ruleID, message)
        
    def getCoverPointName(self, cover_node):
        """Extracts the cover point name from a cover point declaration."""
        # Look for SymbolIdentifier nodes that represent the cover point name
        for identifier in cover_node.iter_find_all({"tag": "SymbolIdentifier"}):
            # The first SymbolIdentifier in a cover point is usually the name
            return identifier.text
        return None