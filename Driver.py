import sys
from antlr4 import *
from Cyclable_Z3_GrammerLexer import Cyclable_Z3_GrammerLexer
from Cyclable_Z3_GrammerParser import Cyclable_Z3_GrammerParser
from Z3_visitor import Z3_visitor


def main(argv):
    input_stream = FileStream(argv[1])
    lexer = Cyclable_Z3_GrammerLexer(input_stream)
    stream = CommonTokenStream(lexer)
    parser = Cyclable_Z3_GrammerParser(stream)
    tree = parser.compilationUnit()

    if parser.getNumberOfSyntaxErrors() > 0:
        print("syntax errors")
    else:
        visitor_interp = Z3_visitor()
        visitor_interp.visit(tree)


if __name__ == '__main__':
    main(sys.argv)
