grammar Cyclable_Z3_Grammer;

// rules
compilationUnit: statement* EOF;

statement:
    check ENDLINE
  | print ENDLINE
  | constAssignment ENDLINE
  | varCreation ENDLINE
  | logicChain ENDLINE
  | mathOperation ENDLINE
  | functionDeclaration ENDLINE
  | functionDefinition;

check            : CHECK;
print            : PRINT (varName | decFunName);

constAssignment  : CONST types varName ASSIGN expr;
varCreation      : types varName;

functionDeclaration: FUN '[' argList ']' types varName;
argList: types (',' types)*;

functionDefinition: TYPES FUNCION ID '(' parametersFunction ')' '{' statement* '}';
parametersFunction: (TYPES ID) (',' TYPES ID)*;

types             : TYPES;
value             : BOOL | NUMBER;
varName           : ID;
assignedName      : ID;
decFunName        : ID '[' parameters ']';
assignedDecFun    : ID '[' parameters ']';
parameters        : (value | varName) (',' (value | varName))*;

logicChain        : logicalItem;
logicalItem       :
    '(' logicalItem ')'
    | NOT logicalItem
    | logicalItem AND logicalItem
    | logicalItem OR logicalItem
    | logicalItem IMPLICATIONS logicalItem
    | (expr | assignedName | assignedDecFun) IMPLICATIONS (expr | assignedName | assignedDecFun)
    | (expr | assignedName | assignedDecFun) COMPARISON (expr | assignedName | assignedDecFun);

mathOperation     : expr;
expr              :
     expr '+' expr
   | expr '*' expr
   | expr '-' expr
   | expr '<<' expr
   | ID
   | NUMBER;

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

NOT : 'not';
AND       : 'and';
OR        : 'or';
IMPLICATIONS: '->';
COMPARISON: '<' | '<=' | '>' | '>=' | '==';

// utilities
fragment IDVALUE: NUMBER | BOOL | ID;
fragment INT: [0-9]+;
NUMBER: INT ('.'(INT)?)?;
BOOL  : 'True' | 'False';

ASSIGN  : '=';

ENDLINE: ';';

ID      : [a-zA-Z_] [a-zA-Z0-9_]*;

WS: [ \t\r\n]+ -> skip;
