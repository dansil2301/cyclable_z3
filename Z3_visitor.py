import z3

from typing import Any

from ConverterHelper import ConverterHelper
from Cyclable_Z3_GrammerParser import Cyclable_Z3_GrammerParser
from Cyclable_Z3_GrammerVisitor import Cyclable_Z3_GrammerVisitor


class Z3_visitor(Cyclable_Z3_GrammerVisitor):
    def __init__(self):
        self.solver = z3.Solver()
        self.model = None

        self.isLocal = False
        self.variables = dict()
        self.local_variables = dict()
        self.functions = dict()

        self.currentFunc = None

    '''
    basic commands
    '''
    def visitCheck(self, ctx: Cyclable_Z3_GrammerParser.CheckContext):
        print(self.solver.check())
        try:
            self.model = self.solver.model()
        except z3.Z3Exception as e:
            self.model = None

    def visitPrint(self, ctx: Cyclable_Z3_GrammerParser.PrintContext):
        lst_var = self.visit(ctx.varList())
        for var in lst_var:
            if isinstance(var, z3.ArithRef):
                if self.model:
                    print(f'{var}: {self.model[var]}')
                else:
                    print(f'{var}: {None}')
            if isinstance(var, tuple):
                func_name, lst_parameters = var
                func = self.variables[func_name]
                if self.model:
                    print(f'{func_name}{lst_parameters}: {self.model.eval(func(*lst_parameters))}')
                else:
                    print(f'{func_name}{lst_parameters}: {None}')

    '''
    helper functions
    '''
    def visitDistinct(self, ctx: Cyclable_Z3_GrammerParser.DistinctContext):
        lst_var = self.visit(ctx.varList())
        n = len(lst_var)
        for i in range(n):
            for j in range(i + 1, n):
                v1 = ConverterHelper.get_var_func(lst_var[i], self.variables)
                v2 = ConverterHelper.get_var_func(lst_var[j], self.variables)
                self.solver.add(v1 != v2)


    '''
    variables assignment
    '''
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

    '''
    logical operation
    '''
    def visitLogicChain(self, ctx: Cyclable_Z3_GrammerParser.LogicChainContext):
        logic_chain = self.visit(ctx.logicalItem())
        if self.isLocal:
            return logic_chain
        else:
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
        elif ctx.getChildCount() == 1:
            return self.visit(ctx.getChild(0))

    '''
    Math operation
    '''
    def visitMathOperation(self, ctx: Cyclable_Z3_GrammerParser.MathOperationContext):
        return self.visit(ctx.expr())

    def visitExpr(self, ctx: Cyclable_Z3_GrammerParser.ExprContext):
        if ctx.getChildCount() == 3:
            if ctx.getChild(0).getText() == "(":
                return self.visit(ctx.getChild(1))
            operator = ctx.getChild(1).getText()
            v1 = self.visit(ctx.getChild(0))
            v2 = self.visit(ctx.getChild(2))
            return ConverterHelper.math_doubles(operator, v1, v2)
        elif ctx.getChildCount() == 1:
            return self.visit(ctx.getChild(0))
    '''
    if elif else
    '''
    def visitIfelse(self, ctx: Cyclable_Z3_GrammerParser.IfelseContext):
        ifelse_exp = None
        else_first = None

        for i in range(ctx.getChildCount() - 2, -1, 3):
            if ctx.getChild(i).getText() == "if":
                condition = self.visit(ctx.getChild(i + 1))
                statements = self.visit(ctx.getChild(i + 2))
            elif ctx.getChild(i).getText() == "elif":
                condition = self.visit(ctx.getChild(i + 1))
                statements = self.visit(ctx.getChild(i + 2))
            elif ctx.getChild(i).getText() == "else":
                else_first = self.visit(ctx.getChild(i + 1))
                print(else_first)
        pass

    def visitIfelseBody(self, ctx: Cyclable_Z3_GrammerParser.IfelseBodyContext):
        statements = []
        for i in range(ctx.getChildCount()):
            statements.append(self.visit(ctx.getChild(i)))
        return statements

    '''
    function creation and calling
    '''
    def visitFunctionDefinition(self, ctx: Cyclable_Z3_GrammerParser.FunctionDefinitionContext):
        func_return_type = self.visit(ctx.z3Type())
        func_name = self.visit(ctx.varName())
        function_parameters = self.visit(ctx.parametersFunction())

        lst_parameters = list(function_parameters.values())
        lst_parameters.append(func_return_type)

        self.local_variables = ConverterHelper.convert_z3types_to_types(function_parameters)
        self.currentFunc = z3.Function(func_name, *lst_parameters)

        self.isLocal = True
        statements = self.visit(ctx.functionBody())
        self.isLocal = False

        self.functions[func_name] = {
            "function": self.currentFunc,
            "variables": self.local_variables,
            "statements": statements
        }
        self.local_variables = dict()

    def visitFunctionBody(self, ctx: Cyclable_Z3_GrammerParser.FunctionBodyContext):
        statements = []
        for i in range(ctx.getChildCount()):
            statements.append(self.visit(ctx.getChild(i)))
        return statements

    def visitFunctionStatement(self, ctx: Cyclable_Z3_GrammerParser.FunctionStatementContext):
        return self.visit(ctx.getChild(0))

    def visitParametersFunction(self, ctx: Cyclable_Z3_GrammerParser.ParametersFunctionContext):
        local_vars = {}
        for i in range(0, ctx.getChildCount(), 3):
            var_type = self.visit(ctx.getChild(i))
            var_name = self.visit(ctx.getChild(i + 1))
            local_vars[var_name] = var_type
        return local_vars

    def visitCallFunction(self, ctx: Cyclable_Z3_GrammerParser.CallFunctionContext):
        func_name = ctx.getChild(0).getText()
        lst_parameters = self.visit(ctx.parameters())
        func_parts = self.functions[func_name]

        fresh_vars = ConverterHelper.fresh_z3types(func_parts['variables'])

        fresh_statements = []
        for statement in func_parts['statements']:
            fresh_statement = ConverterHelper.replace_with_fresh_vars(statement, fresh_vars)
            fresh_statements.append(fresh_statement)

        for i, var in enumerate(fresh_vars):
            if i < len(lst_parameters):
                self.solver.add(fresh_vars[var] == lst_parameters[i])

        function = func_parts['function'](*lst_parameters)
        for statement in fresh_statements:
            self.solver.add(function == statement)

        return function

    '''
    repeater logic
    '''
    def visitRepeater(self, ctx: Cyclable_Z3_GrammerParser.RepeaterContext):
        lst_cycle = self.visit(ctx.getChild(3))
        var_name = self.visit(ctx.varName())

        self.isLocal = True

        for item in lst_cycle:
            self.local_variables[var_name] = item
            self.visit(ctx.repeaterBody())

        self.local_variables = dict()
        self.isLocal = False

    def visitRepeaterBody(self, ctx: Cyclable_Z3_GrammerParser.RepeaterBodyContext):
        statements = []
        for i in range(ctx.getChildCount()):
            result = self.visit(ctx.getChild(i))
            if result is not None:
                self.solver.add(result)
        return statements

    def visitRepeaterStatement(self, ctx: Cyclable_Z3_GrammerParser.RepeaterStatementContext):
        return self.visit(ctx.getChild(0))

    def visitRange(self, ctx: Cyclable_Z3_GrammerParser.RangeContext):
        return self.visit(ctx.rangeValuesParams())

    def visitRangeValuesParams(self, ctx: Cyclable_Z3_GrammerParser.RangeValuesParamsContext):
        values_for_range = []
        for i in range(ctx.getChildCount()):
            if ctx.getChild(i).getText() != ',':
                values_for_range.append(self.visit(ctx.getChild(i)))
        return list(range(*values_for_range))

    def visitRepeaterVarList(self, ctx: Cyclable_Z3_GrammerParser.RepeaterVarListContext):
        return self.visit(ctx.getChild(1))


    '''
    types, values, names, operators
    '''
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
        elif value.isdigit():
            return int(value)
        elif value.split('.')[0].isdigit() and value.split('.')[1].isdigit():
            return float(value)
        return value

    def visitVarName(self, ctx: Cyclable_Z3_GrammerParser.VarNameContext):
        return ctx.getText()

    def visitAssignedName(self, ctx: Cyclable_Z3_GrammerParser.AssignedNameContext):
        var_name = ctx.getText()

        if self.isLocal:
            var = self.local_variables[var_name]
        else:
            var = self.variables[var_name]

        return var

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

    def visitVarList(self, ctx: Cyclable_Z3_GrammerParser.VarListContext):
        lst_var = []
        for i in range(ctx.getChildCount()):
            if ctx.getChild(i).getText() != ',':
                lst_var.append(self.visit(ctx.getChild(i)))
        return lst_var
