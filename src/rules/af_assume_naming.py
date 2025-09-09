# ----------------------------------------------------
# SPDX-FileCopyrightText: AsFigo Technologies, UK
# SPDX-FileCopyrightText: VerifWorks, India
# SPDX-License-Identifier: MIT
# Author: Himank Gangwal, Sep 02, 2025
# ----------------------------------------------------

from af_lint_rule import AsFigoLintRule
import logging
import anytree

class AssumeNaming(AsFigoLintRule):
    """Checks if assume follows a naming convention - start with "m_" """

    def __init__(self, linter):
        self.linter = linter
        self.ruleID = "ASSUME_NAMING"

    def apply(self, filePath: str, data: AsFigoLintRule.VeribleSyntax.SyntaxData):
        for curNode in data.tree.iter_find_all({"tag": "kAssertionItem"}):
            lvLabel = curNode.children[0].text
            lvVerifDirType = curNode.children[1]

            if (not 'kAssumePropertyStatement' in lvVerifDirType.tag):
                continue

            if not lvLabel:
                continue

            if not lvLabel.startswith("m_"):
                message = (
                    f"Debug: Found assume name without m_ prefix. "
                    f"Use m_ as assume prefix. This helps users to "
                    f"look for specific patterns in their log files. "
                    f"Found an Assume as:\n"
                    f"{curNode.text}\n"
                )
                self.linter.logViolation(self.ruleID, message, "WARNING")
        
