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

    @staticmethod
    def fresh_z3types(types):
        converted_types = {}
        for z3type_name in types:
            if str(types[z3type_name].sort()) == "Int":
                converted_types[z3type_name] = z3.FreshInt(z3type_name)
            elif str(types[z3type_name].sort()) == "Bool":
                converted_types[z3type_name] = z3.FreshBool(z3type_name)
            elif str(types[z3type_name].sort()) == "Real":
                converted_types[z3type_name] = z3.FreshReal(z3type_name)
            else:
                converted_types[z3type_name] = None
        return converted_types

    @staticmethod
    def replace_with_fresh_vars(expr, fresh_vars):
        if expr.num_args() > 0:
            args = []
            for i in range(expr.num_args()):
                arg = expr.arg(i)
                if isinstance(arg, (z3.ArithRef, z3.BoolRef)):
                    args.append(ConverterHelper.replace_with_fresh_vars(arg, fresh_vars))
                else:
                    args.append(arg)
            return expr.decl()(*args)

        if isinstance(expr, (z3.ArithRef, z3.BoolRef)):
            var_name = expr.decl().name()
            return fresh_vars.get(var_name, expr)

        return expr

