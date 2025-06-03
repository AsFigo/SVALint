# SVALint
Linter for SystemVerilog Assertions (SVA). Following the philosophy of BYOL - Build Your Own Linter, SVALint is an example of how users can roll out their own linters! 

**SVALint** is an open-source **minimalist** linter tool designed to enforce style and consistency rules for SystemVerilog code. It provides a framework for **Build Your Own Linter** (**BYOL**), allowing users to create their own custom lint rules while benefiting from built-in checks such as proper encapsulation, naming conventions, line spacing, and other cosmetic rules. This linter integrates seamlessly into your development pipeline to ensure consistent, high-quality code.
## Table of Contents
1. [SVALint: SystemVerilog Checker - Linter](#svalint-systemverilog-checker---linter)
2. [BYOL - Build Your Own Linter](#byol---build-your-own-linter)
3. [Open Source](#open-source)
4. [Directory Structure](#directory-structure)
5. [Installation](#installation)
6. [Usage](#usage)   - [Running the Linter from Command Line](#running-the-linter-from-command-line)   - [Running with Makefile (Optional)](#running-with-makefile-optional)   - [Test Cases](#test-cases)
7. [Adding New Lint Rules](#adding-new-lint-rules)
8. [Example Rule (in `src/rules/`)](#example-rule-in-srcrules)
9. [Dependencies](#dependencies)
10. [License](#license)
11. [Credits](#credits)
    
## BYOL - Build Your Own Linter
The core concept of **SVALint** is **BYOL** (Build Your Own Linter), a framework that lets you easily define custom linting rules tailored to your specific needs. Whether it's enforcing naming conventions, checking for proper encapsulation, or any other rule, **SVALint** is flexible and extensible.
With **BYOL**, you can create new rules quickly and add them to your pipeline. The linter is fully customizable, empowering you to ensure that your SystemVerilog code adheres to your specific standards.
## Open Source
This project is **open source** and licensed under the MIT License. Contributions are welcome, and you are free to fork, modify, and distribute it according to your needs. We encourage you to contribute to the community by adding new rules, improving the existing ones, or integrating **SVALint** with other tools and environments.
## Directory Structure
TBD
## Installation
1. Clone the repository:
```bash
git clone https://github.com/AsFigo/svalint.git
cd svalint
```
3. Install required dependencies - Verible mainly

See: https://github.com/chipsalliance/verible

3. pip install anytree
4. pip install tomli
   

## Usage
### Running the Linter from Command Line
The linter can be run using the `svalint.py` script located in the `bin/` directory. This script checks SystemVerilog files against the defined style rules.
1. To run the linter on a specific file:
```bash
python bin/svalint.py -t <path_to_file.sv>
```

### Adding New Lint Rules
1. Create a new Python file inside the `src/rules/` directory. Each file should contain a class that inherits from the base linter class (`AsFigoLinter`).
2. Implement the rule logic in the derived class. Each rule should implement a method like `apply` or `run` to check for the specific violation.
3. After implementing the rule, add the rule to the configuration to enable or disable it.

## Example Rule (in `src/rules/`)
 
## Dependencies
- Python 3.x- Any necessary libraries like `verible_verilog_syntax`

## License
This project is **open source** and licensed under the MIT License. See the [LICENSE](LICENSE) file for details.
---
This **SVALint** linter is part of the **BYOL** (Build Your Own Linter) framework from **AsFigo Technologies**. It's an open-source tool, and we encourage you to contribute to its growth, whether through adding new lint rules, improving existing ones, or enhancing documentation.
Let us know how you're using **SVALint**, and feel free to contribute back to the community!

## Credits
The rules and guidelines in **SVALint** are based on the following sources:
- **SystemVerilog Assertions Handbook***  Ben Cohen, Ajeetha Kumari Venkatesan, Lisa Piper, Srinivasan Venkataramanan: Many of the rules in this linter are inspired by the coding practices and design patterns outlined in this book, which provides a comprehensive approach to SystemVerilog Assertions, focusing on best practices for code quality and maintainability.
- **lowRISC Coding Guidelines**: This linter also draws upon the coding standards and guidelines from the lowRISC project. Their best practices for SystemVerilog coding have been a key resource for defining rules related to naming conventions, encapsulation, and other critical aspects of design quality.
- **Verible**: is an opensource SystemVerilog parser from Google and available via ChipsAlliance
