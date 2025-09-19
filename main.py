# QuantifF(All(), "x", QuantifF(Ex(), "y", ComparF("x", Lt(), "y")))

from syntax import *


def eval(f: Formula) -> bool:
    if isinstance(f, ConstF):
        return f.val
    elif isinstance(f, ComparF):
        if isinstance(f.op, Lt):
            if eval(f.left) == eval(f.right):
                return False
            else:
                raise ValueError(f"Cannot compare {f.left} and {f.right}")
        elif isinstance(f.op, Eq):
            return eval(f.left) == eval(f.right)
        else:
            raise ValueError(f"Unknown comparison operator: {f.op}")
    elif isinstance(f, BoolOpF):
        if isinstance(f.op, Conj):
            return eval(f.left) and eval(f.right)
        elif isinstance(f.op, Disj):
            return eval(f.left) or eval(f.right)
        else:
            raise ValueError(f"Unknown boolean operator: {f.op}")
    elif isinstance(f, NotF):
        return not eval(f.sub)
    elif isinstance(f, str):
        return f
    elif isinstance(f, QuantifF):
        raise ValueError(f"Cannot evaluate quantifier: {f}")
    else:
        raise ValueError(f"Unknown formula: {f}")


formule = ComparF("x", Lt(), "x")
print(formule)
print(eval(formule))

formule1 = conj(ConstF(True), ConstF(False))
print(formule1)
print(eval(formule1))


formule2 = disj(ConstF(True), ConstF(False))
print(formule2)
print(eval(formule2))

formule3 = NotF(ConstF(True))
print(formule3)
print(eval(formule3))
