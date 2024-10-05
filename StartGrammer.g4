grammar StartGrammer;

// rules
compilationUnit: statement* EOF;
statement:
    constAssignment ENDLINE
  | varCreation ENDLINE;

constAssignment  : CONST TYPES ID ASSIGN NUMBER;
varCreation      : TYPES ID;


// tokens
//reserved words
CONST     : 'const';

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
