# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: propositions/operators.py

"""Syntactic conversion of propositional formulas to use only specific sets of
operators."""

from propositions.syntax import *
from propositions.semantics import *

def to_not_and_or(formula: Formula, _rep=None) -> Formula:
    if _rep is None:
        vs = sorted(formula.variables())
        _rep = vs[0] if vs else 'p'

    if is_variable(formula.root):
        return formula

    if is_constant(formula.root):
        x = Formula(_rep)
        if formula.root == 'T':
            return Formula('|', x, Formula('~', x))
        return Formula('&', x, Formula('~', x))

    if is_unary(formula.root):
        return Formula('~', to_not_and_or(formula.first, _rep))

    p = to_not_and_or(formula.first, _rep)
    q = to_not_and_or(formula.second, _rep)

    if formula.root == '&' or formula.root == '|':
        return Formula(formula.root, p, q)

    if formula.root == '->':
        return Formula('|', Formula('~', p), q)

    if formula.root == '+':
        return Formula('|',
                       Formula('&', p, Formula('~', q)),
                       Formula('&', Formula('~', p), q))

    if formula.root == '<->':
        return Formula('|',
                       Formula('&', p, q),
                       Formula('&', Formula('~', p), Formula('~', q)))

    if formula.root == '-&':
        return Formula('~', Formula('&', p, q))

    if formula.root == '-|':
        return Formula('~', Formula('|', p, q))

    raise ValueError('Unknown operator: ' + formula.root)

    # Task 3.5

def to_not_and(formula: Formula, _rep=None) -> Formula:
    if _rep is None:
        vs = sorted(formula.variables())
        _rep = vs[0] if vs else 'p'

    if is_variable(formula.root):
        return formula

    if is_constant(formula.root):
        x = Formula(_rep)
        f = Formula('&', x, Formula('~', x))
        if formula.root == 'T':
            return Formula('~', f)
        return f

    if is_unary(formula.root):
        return Formula('~', to_not_and(formula.first, _rep))

    p = to_not_and(formula.first, _rep)
    q = to_not_and(formula.second, _rep)

    if formula.root == '&':
        return Formula('&', p, q)

    if formula.root == '|':
        return Formula('~', Formula('&', Formula('~', p), Formula('~', q)))

    if formula.root == '->':
        return Formula('~', Formula('&', p, Formula('~', q)))

    if formula.root == '+':
        a = Formula('&', p, Formula('~', q))
        b = Formula('&', Formula('~', p), q)
        return Formula('~', Formula('&', Formula('~', a), Formula('~', b)))

    if formula.root == '<->':
        a = Formula('&', p, q)
        b = Formula('&', Formula('~', p), Formula('~', q))
        return Formula('~', Formula('&', Formula('~', a), Formula('~', b)))

    if formula.root == '-&':
        return Formula('~', Formula('&', p, q))

    if formula.root == '-|':
        orpq = Formula('~', Formula('&', Formula('~', p), Formula('~', q)))
        return Formula('~', orpq)

    raise ValueError('Unknown operator: ' + formula.root)
    # Task 3.6a

def to_nand(formula: Formula, _rep=None, _stage=0) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'-&'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'-&'``.
    """
    if _rep is None:
        vs = sorted(formula.variables())
        _rep = vs[0] if vs else 'p'

    if _stage == 0:
        return to_nand(to_not_and(formula, _rep), _rep, 1)

    if is_variable(formula.root):
        return formula

    if is_constant(formula.root):
        x = Formula(_rep)
        t = Formula('-&', x, Formula('-&', x, x))
        if formula.root == 'T':
            return t
        return Formula('-&', t, t)

    if is_unary(formula.root):
        a = to_nand(formula.first, _rep, 1)
        return Formula('-&', a, a)

    if formula.root == '&':
        a = to_nand(formula.first, _rep, 1)
        b = to_nand(formula.second, _rep, 1)
        t = Formula('-&', a, b)
        return Formula('-&', t, t)

    raise ValueError('Unexpected operator in to_nand: ' + formula.root)
    # Task 3.6b

def to_implies_not(formula: Formula, _rep=None) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'->'`` and ``'~'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'->'`` and ``'~'``.
    """
    if _rep is None:
        vs = sorted(formula.variables())
        _rep = vs[0] if vs else 'p'

    if is_variable(formula.root):
        return formula

    if is_constant(formula.root):
        x = Formula(_rep)
        t = Formula('->', x, x)
        if formula.root == 'T':
            return t
        return Formula('~', t)

    if is_unary(formula.root):
        return Formula('~', to_implies_not(formula.first, _rep))

    p = to_implies_not(formula.first, _rep)
    q = to_implies_not(formula.second, _rep)

    if formula.root == '->':
        return Formula('->', p, q)

    if formula.root == '&':
        return Formula('~', Formula('->', p, Formula('~', q)))

    if formula.root == '|':
        return Formula('->', Formula('~', p), q)

    if formula.root == '-&':
        return Formula('->', p, Formula('~', q))

    if formula.root == '-|':
        return Formula('~', Formula('->', Formula('~', p), q))

    if formula.root == '<->':
        a = Formula('->', p, q)
        b = Formula('->', q, p)
        return Formula('~', Formula('->', a, Formula('~', b)))

    if formula.root == '+':
        a = Formula('->', p, q)
        b = Formula('->', q, p)
        return Formula('->', a, Formula('~', b))

    raise ValueError('Unknown operator: ' + formula.root)
    # Task 3.6c

def to_implies_false(formula: Formula, _rep=None, _stage=0) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'->'`` and ``'F'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'->'`` and ``'F'``.
    """
    if _rep is None:
        vs = sorted(formula.variables())
        _rep = vs[0] if vs else 'p'

    if _stage == 0:
        return to_implies_false(to_implies_not(formula, _rep), _rep, 1)

    if is_variable(formula.root):
        return formula

    if is_constant(formula.root):
        if formula.root == 'F':
            return formula
        return Formula('->', Formula('F'), Formula('F'))

    if is_unary(formula.root):
        return Formula('->', to_implies_false(formula.first, _rep, 1), Formula('F'))

    if formula.root == '->':
        return Formula('->',
                       to_implies_false(formula.first, _rep, 1),
                       to_implies_false(formula.second, _rep, 1))

    raise ValueError('Unexpected operator in to_implies_false: ' + formula.root)
    # Task 3.6d
