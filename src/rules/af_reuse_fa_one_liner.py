# ----------------------------------------------------
# SPDX-FileCopyrightText: AsFigo Technologies, UK
# SPDX-FileCopyrightText: VerifWorks, India
# SPDX-License-Identifier: MIT
# ----------------------------------------------------
from af_lint_rule import AsFigoLintRule
import logging
import anytree

class ReuseNoOneLinerFABLK(AsFigoLintRule):
    """Action block related checks """
  
    def __init__(self, linter):
        self.linter = linter  # Store the linter instance
        self.ruleID = "REUSE_NO_ONE_LINER_FAIL_ABLK"

    def apply(self, filePath: str, data: AsFigoLintRule.VeribleSyntax.SyntaxData):

        for curNode in data.tree.iter_find_all({"tag": "kAssertionItem"}):
            lvSvaCode = curNode.text

            lvAsrtIter = curNode.iter_find_all({"tag": "kAssertPropertyStatement"})
            lvAsrtProp = next(lvAsrtIter, None)
            if lvAsrtProp is None:
                continue

            lvAsrtFailAblkNode = curNode.iter_find_all({"tag": "kElseClause"})
            lvAsrtFailAblkNodeNxt = next(lvAsrtFailAblkNode, None)
            if lvAsrtFailAblkNodeNxt is None:
                continue
            lvFablkType = lvAsrtFailAblkNodeNxt.descendants[2]
            lvFablkTypeName = str(lvFablkType)
            if ('[kSeqBlock]' not in lvFablkTypeName):
                message = (
                    f"REUSE: Found an one-liner fail action block in assert statement.\n"
                    f"Impacts reusability of this code as the error reporting "
                    f"This limits reusability, since future extensions or "
                    f"additional actions cannot be added to the block.\n"
                    f"{lvSvaCode}\n"
                )
                self.linter.logViolation(self.ruleID, message)

