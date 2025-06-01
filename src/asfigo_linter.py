# ----------------------------------------------------
# SPDX-FileCopyrightText: AsFigo Technologies, UK
# SPDX-FileCopyrightText: VerifWorks, India
# SPDX-License-Identifier: MIT
# ----------------------------------------------------

import argparse
import tomli
import os.path
import copy
import functools
from operator import countOf
import operator as op
import logging
import json
import string_utils.validation  as str_val
from af_lint_rule import AsFigoLintRule

class BaseLintLogger:
    def __init__(self, prefix, configFile="config.toml", logLevel=logging.INFO, logFile="svalint_run.log"):
        self.prefix = prefix
        self.logger = logging.getLogger(f"{prefix}Logger")
        self.logger.setLevel(logLevel)

        formatter = logging.Formatter('%(message)s')

        stream_handler = logging.StreamHandler()
        stream_handler.setLevel(logLevel)
        stream_handler.setFormatter(formatter)

        file_handler = logging.FileHandler(logFile, mode='a')
        file_handler.setLevel(logLevel)
        file_handler.setFormatter(formatter)

        if self.logger.hasHandlers():
            self.logger.handlers.clear()

        self.logger.addHandler(stream_handler)
        self.logger.addHandler(file_handler)

        self.rulesConfig = self.loadConfig(configFile)
        self.infoCount = 0
        self.warningCount = 0
        self.errorCount = 0
        self.errorList = []
        self.warningList = []

    '''
    def __init__(self, prefix, configFile="config.toml", logLevel=logging.INFO):
        self.prefix = prefix
        self.logger = logging.getLogger(f"{prefix}Logger")
        self.logger.setLevel(logLevel)
        handler = logging.StreamHandler()
        handler.setLevel(logLevel)
        formatter = logging.Formatter('%(message)s')
        handler.setFormatter(formatter)
        if self.logger.hasHandlers():
            self.logger.handlers.clear()
        self.logger.addHandler(handler)
        self.rulesConfig = self.loadConfig(configFile)
        self.infoCount = 0
        self.warningCount = 0
        self.errorCount = 0
        self.errorList = []     # Store error rule IDs
        self.warningList = []   # Store warning rule IDs
    '''


    def loadConfig(self, configFile):
        try:
            with open(configFile, "rb") as file:
                config = tomli.load(file)
            return config.get("rules", {})
        except FileNotFoundError:
            self.logger.warning(f"{self.prefix}: Config file '{configFile}' not found. Using default settings.")
            return {}

    def ruleEnabled(self, ruleId):
        return self.rulesConfig.get(ruleId, True)

    def logInfo(self, ruleId, msg, severity="INFO"):
        self.infoCount += 1

        logMsg = f"{self.prefix}: INFO: {msg}"
        self.logger.info(logMsg)

    def logViolation(self, ruleId, msg, severity="ERROR"):
        if self.ruleEnabled(ruleId):
            wrapped_msg = msg
            logMsg = f"{self.prefix}: Violation: [{ruleId}]:\n{msg}"

            if severity == "ERROR":
                self.errorCount += 1
                self.errorList.append(ruleId)  # Store error ID
                self.logger.error(logMsg)
            elif severity == "WARNING":
                self.warningCount += 1
                self.warningList.append(ruleId)  # Store warning ID
                self.logger.warning(logMsg)
            else:
                raise ValueError(f"Unsupported severity level: {severity}")
        else:
            self.logger.info(f"{self.prefix}: Rule [{ruleId}] is disabled and will not be logged.")

    def logSummary(self):
        self.logger.info("\n--------------------------------")
        self.logger.info("AsFigo SVALint Report Summary")
        self.logger.info(f"Total lint rules executed: {AsFigoLintRule.get_rule_count()}")

        self.logger.info("--------------------------------")
                # Report counts by severity
        self.logger.info("** Report counts by severity")
        self.logger.info(f"INFO    : {self.infoCount}")
        self.logger.info(f"WARNING : {self.warningCount}")
        self.logger.info(f"ERROR   : {self.errorCount}")

        # Report counts by ID (show each unique rule ID and how many times it was logged)
        self.logger.info("\n** Report counts by ID")
        self._printRuleCounts(self.errorList, "ERROR")
        self._printRuleCounts(self.warningList, "WARNING")

        self.logger.info("--------------------------------\n")

    def _printRuleCounts(self, ruleList, severity):
        ruleDict = {}
        for ruleId in ruleList:
            ruleDict[ruleId] = ruleDict.get(ruleId, 0) + 1
        
        for ruleId, count in sorted(ruleDict.items(), key=lambda x: -x[1]):  # Sort by highest count
            self.logger.info(f"[{ruleId}] {count}")

class AsFigoLinter(BaseLintLogger):
    def __init__(self, configFile="config.toml", logLevel=logging.INFO):
        super().__init__(prefix="AsFigo", configFile=configFile, logLevel=logLevel)
        self.args = self.parseArguments()
        self.testName = self.args.test

    def parseArguments(self):
        parser = argparse.ArgumentParser(description="AsFigoLinter Argument Parser")
        parser.add_argument("-t", "--test", required=True, help="Input test name (file path)")
        return parser.parse_args()

