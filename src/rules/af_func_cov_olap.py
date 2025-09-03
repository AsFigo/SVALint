# ----------------------------------------------------
# SPDX-FileCopyrightText: AsFigo Technologies, UK
# SPDX-FileCopyrightText: VerifWorks, India
# SPDX-License-Identifier: MIT
# ----------------------------------------------------
from af_lint_rule import AsFigoLintRule
import logging
import anytree

class FuncOLAPInCoverProp(AsFigoLintRule):
    """Cover Property with overlapped implicaiton operator leads to false-positives """
  
    def __init__(self, linter):
        self.linter = linter  # Store the linter instance
        self.ruleID = "FUNC_NO_OLAP_COVER"

    def apply(self, filePath: str, data: AsFigoLintRule.VeribleSyntax.SyntaxData):

        for curNode in data.tree.iter_find_all({"tag": "kCoverPropertyStatement"}):
            lvSvaCode = curNode.text
            lvNonOlapImplG = curNode.iter_find_all({"tag": "|->"})
            if (len(list(lvNonOlapImplG)) > 0):
                message = (
                    f"FUNC: Found a overlapped implication operator with "
                    f"cover property directive. This leads to vacuous/bogus "
                    f"functional/assertion/temporal coverage to be collected "
                    f"and reported. This can be a serious hole in the verification "
                    f"process as it gives a false-sense of security/coverage."
                    f"Use ##0 instead. Code snippet: \n"
                    f"{lvSvaCode}\n"
                )
                self.linter.logViolation(self.ruleID, message)

