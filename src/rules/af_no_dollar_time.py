# ----------------------------------------------------
# SPDX-FileCopyrightText: AsFigo Technologies, UK
# SPDX-FileCopyrightText: VerifWorks, India
# SPDX-License-Identifier: MIT
# ----------------------------------------------------

from af_lint_rule import AsFigoLintRule
import logging
import anytree


class UseRealTimeVsTime(AsFigoLintRule):
    """Use $realtime than $time in SVA"""

    def __init__(self, linter):
        self.linter = linter
        # Store the linter instance
        self.ruleID = "FUNC_AVOID_DOLLAR_TIME"

    def apply(
        self, filePath: str, data: AsFigoLintRule.VeribleSyntax.SyntaxData
    ):
        for curNode in data.tree.iter_find_all(
            {"tag": "kPropertyDeclaration"}
        ):
            lvSvaCode = curNode.text
            lvSysTFCall = curNode.iter_find_all({"tag": "kSystemTFCall"})
            for curSysTFName in lvSysTFCall:
                lvSysTFNameIter = curSysTFName.iter_find_all({"tag": "SystemTFIdentifier"})
                lvCurSysTFName = next(lvSysTFNameIter)
                if ('$time' in lvCurSysTFName.text):
                    message = (
                        f"FUNC: Found a call to System function $time "
                        f"inside a SVA property. "
                        f"Timing checks should be performed using realtime than "
                        f"$time. See: below discussion to appreciate the rationale: \n"
                        f"https://verificationacademy.com/forums/t/sva-for-delayed-state-transition-from-fault-id-to-wait-state-100ms-delay/51322 \n"
                        f"{lvSvaCode}\n"
                    )

                    self.linter.logViolation(self.ruleID, message)
