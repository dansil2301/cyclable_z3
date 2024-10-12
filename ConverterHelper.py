import z3

from typing import Any


class ConverterHelper:
    @staticmethod
    def logic_doubles(operator, left, right):
        if operator == '<':
            return left < right
        elif operator == '<=':
            return left <= right
        elif operator == '>':
            return left > right
        elif operator == '>=':
            return left >= right
        elif operator == '==':
            return left == right
        elif operator == '!=':
            return left != right
        elif operator == 'and':
            return z3.And(left, right)
        elif operator == 'or':
            return z3.Or(left, right)
        elif operator == '->':
            return z3.Implies(left, right)
        else:
            return None

    @staticmethod
    def logic_single(operator, v1):
        if operator == 'not':
            return z3.Not(v1)

    @staticmethod
    def math_doubles(operator, left, right):
        if operator == '+':
            return left + right
        elif operator == '-':
            return left - right
        elif operator == '*':
            return left * right
        elif operator == '<<':
            return left << right
        else:
            return None

    @staticmethod
    def convert_z3types_to_types(types):
        converted_types = {}
        for z3type_name in types:
            if str(types[z3type_name]) == "Int":
                converted_types[z3type_name] = z3.Int(z3type_name)
            elif str(types[z3type_name]) == "Bool":
                converted_types[z3type_name] = z3.Bool(z3type_name)
            elif str(types[z3type_name]) == "Real":
                converted_types[z3type_name] = z3.Real(z3type_name)
            else:
                converted_types[z3type_name] = None
        return converted_types

