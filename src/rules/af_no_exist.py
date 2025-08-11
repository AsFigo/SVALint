# ----------------------------------------------------
# SPDX-FileCopyrightText: AsFigo Technologies, UK
# SPDX-FileCopyrightText: VerifWorks, India
# SPDX-License-Identifier: MIT
# Author: Himank Gangwal, August 11, 2025
# ----------------------------------------------------

from af_lint_rule import AsFigoLintRule
import logging
import anytree

class NoExists(AsFigoLintRule):
    """Checks if .exist() is in the code """

    def __init__(self, linter):
        self.linter = linter
        self.ruleID = "NO_EXISTS"

    def apply(self, filePath: str, data: AsFigoLintRule.VeribleSyntax.SyntaxData):
        for curNode in data.tree.iter_find_all({"tag": ["kHierarchyExtension"]}):
            lvSvaCode = self.getHeaderName(curNode)
            if(lvSvaCode == "exists"):
                message = (
                    f"Debug: Found .exists() in the code. Don't use it\n"
                )

                self.linter.logViolation(self.ruleID, message)
                
    def getHeaderName(self, header):
        for identifier in header.iter_find_all({"tag": "SymbolIdentifier"}):
            return identifier.text
        return "Unknown"
    
    def getSymbolIdentifierNames(self, header):
        retval = []
        for identifier in header.iter_find_all({"tag": "SymbolIdentifier"}):
            retval.append(identifier.text)
        if len(retval) > 0:
            return retval
        else:
            return "Unknown"