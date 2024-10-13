grammar Cyclable_Z3_Grammer;

// rules
compilationUnit: statement* EOF;

statement:
    check ENDLINE
  | print ENDLINE
  | callFunction ENDLINE
  | constAssignment ENDLINE
  | varCreation ENDLINE
  | mathOperation ENDLINE
  | logicChain ENDLINE
  | functionDeclaration ENDLINE
  | distinct ENDLINE
  | functionDefinition
  ;

functionStatement:
  mathOperation ENDLINE
  | logicChain ENDLINE
  | distinct;

check            : CHECK;
print            : PRINT varList;

distinct         : DISTINCT varList;
varList          : (assignedName | decFunName) (',' (assignedName | decFunName))*;

constAssignment  : CONST types varName ASSIGN expr;
varCreation      : types varName;

functionDeclaration: FUN '[' argList ']' z3Type varName;
argList: z3Type (',' z3Type)*;

functionDefinition: z3Type FUNCION varName '(' parametersFunction ')' '{' functionBody '}';
functionBody      : functionStatement*;
parametersFunction: (z3Type varName) (',' z3Type varName)*;

z3Type            : TYPES;
types             : TYPES;
value             : BOOL | NUMBER;
varName           : ID;
assignedName      : ID;
decFunName        : ID '[' parameters ']';
assignedDecFun    : ID '[' parameters ']';
callFunction      : ID '(' parameters ')';
parameters        : (value | assignedName) (',' (value | assignedName))*;

mathOperation     : expr;
expr              :
   '(' expr ')'
   | expr '+' expr
   | expr '*' expr
   | expr '-' expr
   | expr '<<' expr
   | assignedName
   | value;

logicChain        : logicalItem;
logicalItem       :
    '(' logicalItem ')'
    | NOT logicalItem
    | logicalItem AND logicalItem
    | logicalItem OR logicalItem
    | logicalItem IMPLICATIONS logicalItem
    | logicalItem IMPLICATIONS logicalItem
    | logicalItem COMPARISON logicalItem
    | (value | assignedName | expr | assignedDecFun | callFunction);

// tokens
// reserved words
CHECK     : 'check';
PRINT     : 'print';

CONST     : 'const';
FUN       : 'Fun';
FUNCION   : 'function' ;

DISTINCT  : 'distinct';

TYPES     : INT_T | BOOL_T | REAL_T;
INT_T     : 'Int';
BOOL_T    : 'Bool';
REAL_T    : 'Float';

NOT : 'not';
AND       : 'and';
OR        : 'or';
IMPLICATIONS: '->';
COMPARISON: '<' | '<=' | '>' | '>=' | '==' | '!=';

// utilities
fragment IDVALUE: NUMBER | BOOL | ID;
fragment INT: [0-9]+;
NUMBER: INT ('.'(INT)?)?;
BOOL  : 'True' | 'False';

ASSIGN  : '=';

ENDLINE: ';';

ID      : [a-zA-Z_] [a-zA-Z0-9_]*;

WS: [ \t\r\n]+ -> skip;
