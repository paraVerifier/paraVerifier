#coding=utf-8

"""
Functions for checking smt2 formulae

@author Yongjian Li <lyj238@gmail.com>
@author Kaiqiang Duan <duankq@ios.ac.cn>
"""

from z3 import Solver, parse_smt2_string

class SMT2(object):
    def __init__(self, context):
        super(SMT2, self).__init__()
        self.context = context

    def check(self, smt2_formula, context=None):
        s = Solver()
        s.add(parse_smt2_string((context if context else self.context) + smt2_formula))
        return str(s.check())
