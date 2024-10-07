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
        try:
            self.model = self.solver.model()
        except z3.Z3Exception as e:
            self.model = None

    def visitPrint(self, ctx: Cyclable_Z3_GrammerParser.PrintContext):
        var_name = self.visit(ctx.varName())
        var = self.variables[var_name]
        if self.model:
            print(f'{var_name}: {self.model[var]}')
        else:
            print(f'{var_name}: {None}')

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

    # logical operation
    def visitLogicChain(self, ctx: Cyclable_Z3_GrammerParser.LogicChainContext):
        logic_chain = self.visit(ctx.logicalItem())
        print(logic_chain)
        self.solver.add(logic_chain)

    def visitLogicalItem(self, ctx: Cyclable_Z3_GrammerParser.LogicalItemContext):
        if ctx.getChild(0).getText() == "(":
            return self.visit(ctx.getChild(1))

        operator = ctx.getChild(1).getText()
        if operator == '<':
            return self.visit(ctx.getChild(0)) < self.visit(ctx.getChild(2))
        elif operator == '<=':
            return self.visit(ctx.getChild(0)) <= self.visit(ctx.getChild(2))
        elif operator == '>':
            return self.visit(ctx.getChild(0)) > self.visit(ctx.getChild(2))
        elif operator == '>=':
            return self.visit(ctx.getChild(0)) >= self.visit(ctx.getChild(2))
        elif operator == '==':
            return self.visit(ctx.getChild(0)) == self.visit(ctx.getChild(2))
        elif operator == 'and':
            return z3.And(self.visit(ctx.getChild(0)), self.visit(ctx.getChild(2)))
        elif operator == 'or':
            return z3.Or(self.visit(ctx.getChild(0)), self.visit(ctx.getChild(2)))

    # types, values, names, operators
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

    def visitMathValue(self, ctx: Cyclable_Z3_GrammerParser.MathValueContext):
        value = ctx.getText()
        if value == 'True' or value == 'False':
            return z3.Bool(bool(value))
        elif value.isdigit() or all(part.isdigit() for part in value.split('.')):
            return float(value)
        else:
            return None

    def visitVarName(self, ctx: Cyclable_Z3_GrammerParser.VarNameContext):
        return ctx.getText()

    def visitAssignedName(self, ctx: Cyclable_Z3_GrammerParser.AssignedNameContext):
        var_name = ctx.getText()
        return self.variables[var_name]
