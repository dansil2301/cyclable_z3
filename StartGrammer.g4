grammar StartGrammer;

// rules
compilationUnit: statement* EOF;

statement:
    constAssignment ENDLINE
  | varCreation ENDLINE
  | functionDeclaration ENDLINE
  | functionDefinition;

constAssignment  : CONST TYPES ID ASSIGN NUMBER;
varCreation      : TYPES ID;

functionDeclaration: FUN '[' argList ']' ID;
argList: TYPES (',' TYPES)*;

functionDefinition: TYPES FUNCION ID '(' parametersFunction ')' '{' statement* '}';
parametersFunction: (TYPES ID)* (',' TYPES ID)*;

// tokens
//reserved words
CONST     : 'const';
FUN       : 'Fun';
FUNCION   : 'function' ;

TYPES     : INT_T | BOOL_T | REAL_T;
INT_T     : 'Int';
BOOL_T    : 'Bool';
REAL_T    : 'Float';

ID      : [a-zA-Z_] [a-zA-Z0-9_]*;

ASSIGN  : '=';

fragment INT: [0-9]+;
NUMBER: INT ('.'(INT)?)?;

ENDLINE: ';';

WS: [ \t\r\n]+ -> skip;
