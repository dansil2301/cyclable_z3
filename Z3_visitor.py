import z3

from typing import Any
from Cyclable_Z3_GrammerParser import Cyclable_Z3_GrammerParser
from Cyclable_Z3_GrammerVisitor import Cyclable_Z3_GrammerVisitor


class Z3_visitor(Cyclable_Z3_GrammerVisitor):
    def __init__(self):
        self.solver = z3.Solver()
        self.model = None

        self.variables = dict()

    def visitCheck(self, ctx: Cyclable_Z3_GrammerParser.CheckContext):
        print(self.solver.check())
        self.model = self.solver.model()

    def visitPrint(self, ctx: Cyclable_Z3_GrammerParser.PrintContext):
        var_name = self.visit(ctx.varName())
        var = self.variables[var_name]
        print(self.model[var])

    # Variables main logic
    def visitConstAssignment(self, ctx: Cyclable_Z3_GrammerParser.ConstAssignmentContext):
        var_type = self.visit(ctx.types())
        var_name = self.visit(ctx.varName())
        var_value = self.visit(ctx.value())

        var = var_type(var_name)
        self.solver.add(var == var_value)
        self.variables[var_name] = var

    def visitVarCreation(self, ctx: Cyclable_Z3_GrammerParser.VarCreationContext):
        var_type = self.visit(ctx.types())
        var_name = self.visit(ctx.varName())

        var = var_type(var_name)
        self.variables[var_name] = var

    def visitTypes(self, ctx: Cyclable_Z3_GrammerParser.TypesContext):
        var_type = ctx.getText()
        if var_type == 'Int':
            return z3.Int
        elif var_type == 'Bool':
            return z3.Bool
        elif var_type == 'Float':
            return z3.Real
        else:
            return None

    def visitValue(self, ctx: Cyclable_Z3_GrammerParser.ValueContext):
        return ctx.getText()

    def visitVarName(self, ctx: Cyclable_Z3_GrammerParser.VarNameContext):
        return ctx.getText()
