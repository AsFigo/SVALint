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

    lvMsg = """
Rule suggested by Ben Cohen:

IEEE LRM 1800 states:

16.6 Boolean expressions: “Elements of dynamic arrays, queues, and associative arrays that are sampled for assertion expression evaluation may get removed from the array or the array may get resized before the assertion expression is evaluated. These specific array elements sampled for assertion expression evaluation shall continue to exist within the scope of the assertion until the assertion expression evaluation completes.”

Many tools are slow to adopt this IEEE 1800 requirement. Several imposed restrictions on the use of associative arrays within assertions, and some prohibited them entirely, likely due to performance concerns.

So avoid usage of array.exists() method call in SVA

e.g.
((valid, v_err=mem_aarray.exists(addr))
    """
    def __init__(self, linter):
        self.linter = linter
        self.ruleID = "NO_AA_EXISTS_SVA"

    def apply(self, filePath: str, data: AsFigoLintRule.VeribleSyntax.SyntaxData):
        for curNode in data.tree.iter_find_all({"tag": ["kPropertyDeclaration"]}):
            for hierNode in curNode.iter_find_all({"tag": ["kHierarchyExtension"]}):
                # check if the node contains "exists"
                if self.containsExists(hierNode):
                    message = (
                        f"{self.lvMsg}"
                        f"COMPAT: Found .exists() in the code. \n"
                        f"{curNode.text}"
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
