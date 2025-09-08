# ----------------------------------------------------
# SPDX-FileCopyrightText: AsFigo Technologies, UK
# SPDX-FileCopyrightText: VerifWorks, India
# SPDX-License-Identifier: MIT
# Author: Himank Gangwal, Sep 02, 2025
# ----------------------------------------------------

from af_lint_rule import AsFigoLintRule
import logging
import anytree

class AvoidAAExistsSVA(AsFigoLintRule):
    """Checks if Assoc array method exist() is in the SVA code """

    def __init__(self, linter):
        self.linter = linter
        self.ruleID = "NO_AA_EXISTS_SVA"

    def apply(self, filePath: str, data: AsFigoLintRule.VeribleSyntax.SyntaxData):
        for curNode in data.tree.iter_find_all({"tag": ["kPropertyDeclaration"]}):
            for hierNode in curNode.iter_find_all({"tag": ["kHierarchyExtension"]}):
                # check if the node contains "exists"
                if self.containsExists(hierNode):
                    message = (
                        f"Debug: Found .exists() in the code. Don't use it\n"
                    )
                    self.linter.logViolation(self.ruleID, message)
                
    def containsExists(self, node):
        """Checks if a node or its children contain 'exists' usage."""
        # Check the current node's text
        if hasattr(node, 'text') and 'exists' in node.text:
            return True
        
        # Check all SymbolIdentifier nodes in this hierarchy
        for identifier in node.iter_find_all({"tag": "SymbolIdentifier"}):
            if identifier.text == "exists":
                return True
        
        return False
