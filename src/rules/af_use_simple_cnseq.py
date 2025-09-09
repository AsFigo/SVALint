# ----------------------------------------------------
# SPDX-FileCopyrightText: AsFigo Technologies, UK
# SPDX-FileCopyrightText: VerifWorks, India
# SPDX-License-Identifier: MIT
# ----------------------------------------------------

from af_lint_rule import AsFigoLintRule
import logging
import anytree


class UseSimpleExprConseq(AsFigoLintRule):
    lvMsg = """

  Found complex consequent expression inside a property definition. 
  It is highly recommended to use many simple propertie than a 
  monolithic, complex one. This helps in debug as the failures can 
  spot specific signal/expression failing. 

    """

    def __init__(self, linter):
        self.linter = linter
        # Store the linter instance
        self.ruleID = "DBG_USE_SIMPLE_EXPR_IN_CONSEQ"

    def apply(self, filePath: str, data: AsFigoLintRule.VeribleSyntax.SyntaxData):

        for curNode in data.tree.iter_find_all({"tag": "kPropertyDeclaration"}):
            lvSvaCode = curNode.text
            lvNumOlapOper = len(list(curNode.iter_find_all({"tag": "|->"})))
            lvNumNonOlapOper = len(list(curNode.iter_find_all({"tag": "|=>"})))

            if (lvNumOlapOper + lvNumNonOlapOper  > 1):
                message = f"{self.lvMsg}\n" f"{lvSvaCode}\n"
                self.linter.logViolation(self.ruleID, message)
                continue

            for lvOlapImplNode in curNode.iter_find_all({"tag": "|->"}):
                lvConseqNode = lvOlapImplNode.siblings[1]
                lvConseqExprANDG = lvConseqNode.iter_find_all({"tag": "&&"})
                lvNumANDinConseq = len(list(lvConseqExprANDG))
                if (lvNumANDinConseq > 2):
                    message = f"{self.lvMsg}\n" f"{lvSvaCode}\n"
                    self.linter.logViolation(self.ruleID, message)
