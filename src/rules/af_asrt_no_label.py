# ----------------------------------------------------
# SPDX-FileCopyrightText: AsFigo Technologies, UK
# SPDX-FileCopyrightText: VerifWorks, India
# SPDX-License-Identifier: MIT
# ----------------------------------------------------

from af_lint_rule import AsFigoLintRule
import logging
import anytree

class MissingLabelChk(AsFigoLintRule):
    """Enhance debug-ability of assertions by using labels """
    def af_dbg_print_tree(self, data):
        if not data.tree:
            return
        for prefix, _, node in anytree.RenderTree(data.tree):
            print(f"\033[90m{prefix}\033[0m{node.to_formatted_string()}")
  
    def __init__(self, linter):
        self.linter = linter  # Store the linter instance
        self.ruleID = "ASSERT_MISSING_LABEL"

    def apply(self, filePath: str, data: AsFigoLintRule.VeribleSyntax.SyntaxData):

        for curNode in data.tree.iter_find_all({"tag": "kAssertionItem"}):
          lvSvaCode = curNode.text
          lvAsrtLabel =  curNode.children[0]
          if (( ":" not in lvAsrtLabel.text)):
                message = (
                    f"Error: Missing label for an assert statement.\n"
                    f"{lvSvaCode}\n"
                )
                self.linter.logViolation(self.ruleID, message)


