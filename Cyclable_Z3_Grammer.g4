grammar Cyclable_Z3_Grammer;

// rules
compilationUnit: statement* EOF;

statement:
    check ENDLINE
  | print ENDLINE
  | constAssignment ENDLINE
  | varCreation ENDLINE
  | logicChain ENDLINE
  | functionDeclaration ENDLINE
  | functionDefinition;

check            : CHECK;
print            : PRINT varName;

constAssignment  : CONST types varName ASSIGN value;
varCreation      : types varName;

functionDeclaration: FUN '[' argList ']' ID;
argList: TYPES (',' TYPES)*;

functionDefinition: TYPES FUNCION ID '(' parametersFunction ')' '{' statement* '}';
parametersFunction: (TYPES ID) (',' TYPES ID)*;

types             : TYPES;
value             : NUMBER | BOOL;
varName           : ID;
assignedName      : ID;

logicChain        : logicalItem;
logicalItem       :
    '(' logicalItem ')'
    | SINGLECOM logicalItem
    | logicalItem AND logicalItem
    | logicalItem OR logicalItem
    | (value | assignedName) COMPARISON (value | assignedName);

// tokens
// reserved words
CHECK     : 'check';
PRINT     : 'print';

CONST     : 'const';
FUN       : 'Fun';
FUNCION   : 'function' ;

TYPES     : INT_T | BOOL_T | REAL_T;
INT_T     : 'Int';
BOOL_T    : 'Bool';
REAL_T    : 'Float';

AND       : 'and';
OR        : 'or';
COMPARISON: '<' | '<=' | '>' | '>=' | '==';
SINGLECOM : 'not';

// utilities
ID      : [a-zA-Z_] [a-zA-Z0-9_]*;

ASSIGN  : '=';

fragment IDVALUE: NUMBER | BOOL | ID;
fragment INT: [0-9]+;
NUMBER: INT ('.'(INT)?)?;
BOOL  : 'True' | 'False';

ENDLINE: ';';

WS: [ \t\r\n]+ -> skip;
