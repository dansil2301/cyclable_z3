grammar StartGrammer;

// rules
compilationUnit: statement* EOF;
statement:
    constAssignment ENDLINE
  | varCreation ENDLINE
  | functionDeclaration ENDLINE
  | functionDefinition ENDLINE;

constAssignment  : CONST TYPES ID ASSIGN NUMBER;
varCreation      : TYPES ID;
functionDeclaration: FUN '[' argList ']' ID;
functionDefinition: TYPES FUNC ID '(' TYPES ID ')'; //not sure how to do {1 < name or -1 > name;}
argList: TYPES (',' TYPES)*;


// tokens
//reserved words
CONST     : 'const';
FUN : 'Fun';
FUNC : 'function' ;

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
