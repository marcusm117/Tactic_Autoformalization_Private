---
alwaysApply: true
---
## Conda Environment

**ALWAYS** first activate the conda environment for this project!!!

conda activate afc

You **MUST** run this before you run any other command!!! My conda is installed in `~/anaconda3/`.


## Documentation

Whenever you edit or make updates to a source code file, you **MUST** update the comments, docstrings, and other documentation to reflect the changes you made.


## Don't Touch Existing Comments Unless Told

You should **never** touch or delete existing comments unless told to do so!!!!!!!!!!




---
description: 
globs: *.py
alwaysApply: false
---
## Python

Whenenver you create and change any .py files, or write any Python code, you should always follow the code style specified below.

### Logging

Always use lazy % formatting in logging instead of f-strings!!! You **MUST** do it like this: `logging.info("Hello, %s!", name)`!!!


### PEP 585 – Type Hinting Generics In Standard Collections

https://peps.python.org/pep-0585/

Static typing as defined by PEPs 484, 526, 544, 560, and 563 was built incrementally on top of the existing Python runtime and constrained by existing syntax and runtime behavior. This led to the existence of a duplicated collection hierarchy in the typing module due to generics (for example typing.List and the built-in list, typing.Union and built-in |, typing.Optional and built-in | None)

In short, don't ever use `from typing import Any, Dict, List, Optional, Tuple, Union`!!! Use the native types whenever possible!!! For `Optional`, use `| None` instead of `Optional[T]`!!!


### Authorship, License, and Import Style

Always include the authorship and license in the header of the file, the defaults are in the example below. There **MUST** be 2 blank lines between the authorship and license and the imports. Always use the following import style: standard library modules first, then external modules, then internal modules. List all imports in each section in **alphabetical order**.
```python
# Authors: name
# License: Apache 2.0


# Standard Library Modules
import argparse
import csv
from pathlib import Path
from zipfile import ZipFile

# External Modules
import aiofiles
import aiohttp
from dotenv import load_dotenv
from tqdm import tqdm

# Internal Modules
```




---
description: 
globs: *.py,*.lean
alwaysApply: false
---
## Python
Whenenver you change any .py files, you should always format it using black, lint it using flake8 and pylint, type checking it with mypy. You should fix all issues reported, run all commands again, fix all issues reported, until there's none.

LINE_LENGTH = 150

### Formatting
Step 1: use black to format all Python files you have changed.

LINE_LENGTH = 150
python -m black --line-length $(LINE_LENGTH) `the_python_files_you_have_changed`

### Linting
Step 2: use flake8 and pylint to lint all Python files you have changed.

LINE_LENGTH = 150
python -m black --check --line-length $(LINE_LENGTH) `the_python_files_you_have_changed`
python -m flake8 --max-line-length=$(LINE_LENGTH) --extend-ignore=E203,BLK100 a3j `the_python_files_you_have_changed`
python -m pylint --max-line-length=$(LINE_LENGTH) --disable=C0301,C0302,R1720,C0114,C0115,C0116,C0103,W1114,W0719,W0718,R0914,R0913,R0915,R0917,R0801,E0401 `the_python_files_you_have_changed`

### Type Checking
Step 3: use mypy to type check all Python files you have changed.

python -m mypy `the_python_files_you_have_changed`

### Aborting

You should try your best to fix any issues reported by the linters and type checker. However, if there's some packages missing type stubs and you really can't install it after 3 attempts, then just abort and report back to me!!!

### Asking Confirmation

If the reported issue is minor or you are confident about your planned fix, just go fix them without asking my confirmation!!! Only reported back to me if you are not sure how to fix the issue or there are multiple ways for me to decide!!!

### Many-File Alternative

If you have changed many files, you can just go back to the project root directory and run `make fix` and then `make lint` and `make type`


## Lean

Whenver you changed any .lean files, you should always build it using lake. You should fix all issues reported, run all commands again, fix all issues reported, until there's none.

### Compiling
Step 1: use lake to build the lean project folder where the files you changed live in.

lake build `the_folder_of_files_you_have_changed`

For example, if you changed `LeanEuclid_Customized/E3/Engine/EquivCheck.lean`, then go to `LeanEuclid_Customized` and run `lake build E3`.

### Asking Confirmation

If the reported issue is minor or you are confident about your planned fix, just go fix them without asking my confirmation!!! Only reported back to me if you are not sure how to fix the issue or there are multiple ways for me to decide!!!
