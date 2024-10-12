import z3

from typing import Any

from ConverterHelper import ConverterHelper
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
        var_type = ctx.getChild(1)
        if type(var_type) is Cyclable_Z3_GrammerParser.varName:
            var_name = self.visit(ctx.varName())
            var = self.variables[var_name]
            if self.model:
                print(f'{var_name}: {self.model[var]}')
            else:
                print(f'{var_name}: {None}')
        if type(var_type) is Cyclable_Z3_GrammerParser.DecFunNameContext:
            func_name, lst_parameters = self.visit(ctx.decFunName())
            func = self.variables[func_name]
            if self.model:
                print(f'{func_name}{lst_parameters}: {self.model.eval(func(*lst_parameters))}')
            else:
                print(f'{func_name}{lst_parameters}: {None}')

    # Variables main logic
    def visitConstAssignment(self, ctx: Cyclable_Z3_GrammerParser.ConstAssignmentContext):
        var_type = self.visit(ctx.types())
        var_name = self.visit(ctx.varName())
        var_value = self.visit(ctx.expr())
        var = var_type(var_name)

        self.solver.add(var == var_value)
        self.variables[var_name] = var

    def visitVarCreation(self, ctx: Cyclable_Z3_GrammerParser.VarCreationContext):
        var_type = self.visit(ctx.types())
        var_name = self.visit(ctx.varName())

        var = var_type(var_name)
        self.variables[var_name] = var

    def visitFunctionDeclaration(self, ctx: Cyclable_Z3_GrammerParser.FunctionDeclarationContext):
        func_return_type = self.visit(ctx.z3Type())
        func_name = self.visit(ctx.varName())
        parameters = self.visit(ctx.argList())

        parameters.append(func_return_type)
        chain_parameters = parameters
        func = z3.Function(func_name, *chain_parameters)
        self.variables[func_name] = func

    def visitArgList(self, ctx: Cyclable_Z3_GrammerParser.ArgListContext):
        lst_types = []
        for i in range(ctx.getChildCount()):
            if ctx.getChild(i).getText() != ',':
                lst_types.append(self.visit(ctx.getChild(i)))
        return lst_types

    # logical operation
    def visitLogicChain(self, ctx: Cyclable_Z3_GrammerParser.LogicChainContext):
        logic_chain = self.visit(ctx.logicalItem())
        self.solver.add(logic_chain)

    def visitLogicalItem(self, ctx: Cyclable_Z3_GrammerParser.LogicalItemContext):
        if ctx.getChildCount() == 3:
            if ctx.getChild(0).getText() == "(":
                return self.visit(ctx.getChild(1))
            operator = ctx.getChild(1).getText()
            v1 = self.visit(ctx.getChild(0))
            v2 = self.visit(ctx.getChild(2))
            return ConverterHelper.logic_doubles(operator, v1, v2)
        elif ctx.getChildCount() == 2:
            operator = ctx.getChild(0).getText()
            v1 = self.visit(ctx.getChild(1))
            return ConverterHelper.logic_single(operator, v1)

    def visitMathOperation(self, ctx: Cyclable_Z3_GrammerParser.MathOperationContext):
        return self.visit(ctx.expr())

    def visitExpr(self, ctx: Cyclable_Z3_GrammerParser.ExprContext):
        if ctx.getChildCount() == 3:
            operator = ctx.getChild(1).getText()
            v1 = self.visit(ctx.getChild(0))
            v2 = self.visit(ctx.getChild(2))
            return ConverterHelper.math_doubles(operator, v1, v2)
        elif ctx.getChildCount() == 1:
            token_text = ctx.getChild(0).getText()
            if token_text.isdigit():
                return int(token_text)
            else:
                return self.variables.get(token_text, None)

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

    def visitZ3Type(self, ctx: Cyclable_Z3_GrammerParser.Z3TypeContext):
        var_type = ctx.getText()
        if var_type == 'Int':
            return z3.IntSort()
        elif var_type == 'Bool':
            return z3.BoolSort()
        elif var_type == 'Float':
            return z3.RealSort()
        else:
            return None

    def visitValue(self, ctx: Cyclable_Z3_GrammerParser.ValueContext):
        value = ctx.getText()
        if 'True' == value or 'False' == value:
            value = bool(value)
        return value

    def visitVarName(self, ctx: Cyclable_Z3_GrammerParser.VarNameContext):
        return ctx.getText()

    def visitAssignedName(self, ctx: Cyclable_Z3_GrammerParser.AssignedNameContext):
        var_name = ctx.getText()
        return self.variables[var_name]

    def visitAssignedDecFun(self, ctx: Cyclable_Z3_GrammerParser.AssignedDecFunContext):
        func_name = ctx.getChild(0).getText()
        lst_parameters = self.visit(ctx.parameters())

        decl_func = self.variables[func_name]
        return decl_func(*lst_parameters)

    def visitDecFunName(self, ctx: Cyclable_Z3_GrammerParser.DecFunNameContext):
        func_name = ctx.getChild(0).getText()
        lst_parameters = self.visit(ctx.parameters())
        return func_name, lst_parameters

    def visitParameters(self, ctx: Cyclable_Z3_GrammerParser.ParametersContext):
        lst_parameters = []
        for i in range(ctx.getChildCount()):
            if ctx.getChild(i).getText() != ",":
                lst_parameters.append(self.visit(ctx.getChild(i)))
        return lst_parameters
