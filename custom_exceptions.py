class InvalidIndexException(Exception):
    def __init__(self, idx=None):
        self.msg = 'InvalidIndexException ocurred'
        self.idx = idx

    def __str__(self):
        return self.msg + f": invalid index {self.idx}" if self.idx is not None else ""

class InvalidValueException(Exception):
    def __init__(self, val=None):
        self.msg = 'InvalidValueException ocurred'
        self.val = val

    def __str__(self):
        return self.msg + f": invalid value {self.val}" if self.val is not None else ""

class InvalidTypeException(Exception):
    def __init__(self, varname=None, right=None, wrong=None):
        self.msg = 'InvalidTypeException ocurred'
        self.varname = varname
        self.right = right
        self.wrong = wrong

    def __str__(self):
        return self.msg + f": type of variable " if self.varname is None else f"type of '{self.varname}' "    \
                        + f"needs to be other type " if self.right is None else f"needs to be {self.right} "  \
                        + f"" if self.wrong is None else f", not {self.wrong}"

class InvalidTargetStringException(Exception):
    def __init__(self, val=None):
        self.msg = 'InvalidTargetStringException ocurred'
        self.val = val

    def __str__(self):
        return self.msg + f": invalid target string {self.val}" if self.val is not None else ""

class DcareDismatchException(Exception):
    def __init__(self, msg="dont care term is dismatched (use ignore_dcare flag or inclusive_dcare flag)"):
        self.msg = f'DcareDismatchException ocurred: {msg}'

    def __str__(self):
        return self.msg

class BitsizDismatchException(Exception):
    def __init__(self, msg="bitsize is dismatched"):
        self.msg = f'BitsizDismatchException ocurred: {msg}'

    def __str__(self):
        return self.msg

class InvalidBinValueException(Exception):
    def __init__(self, msg="invalid binary value"):
        self.msg = f'InvalidBinValueException ocurred: {msg}'

    def __str__(self):
        return self.msg

class InvalidImplicantException(Exception):
    def __init__(self, msg="invalid implicant"):
        self.msg = f'InvalidImplicantException ocurred: {msg}'

    def __str__(self):
        return self.msg


class InvalidSequenceException(Exception):
    def __init__(self, msg="invalid sequence"):
        self.msg = f'InvalidSequenceException ocurred: {msg}'

    def __str__(self):
        return self.msg

