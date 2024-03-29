/*
BSD License

Copyright (c) 2013, Tom Everett
All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions
are met:

1. Redistributions of source code must retain the above copyright
   notice, this list of conditions and the following disclaimer.
2. Redistributions in binary form must reproduce the above copyright
   notice, this list of conditions and the following disclaimer in the
   documentation and/or other materials provided with the distribution.
3. Neither the name of Tom Everett nor the names of its contributors
   may be used to endorse or promote products derived from this software
   without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
"AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*/

grammar TinyC;

program: (procedure|assignment)+ EOF;

procedure
   : (type|VOID) name=id '(' a=binders?  ')'
       ('[' 'pre'        pre=expr ']')?
       ('[' 'post'       post=expr ']')?
       ('[' 'modifies'   modifies=ids ']')?
      (body|';')
   ;

binders: type id (',' type id)*;
ids: id (',' id)*;


ifStatement
   : 'if' '(' expr ')' statement
   | 'if' '(' expr ')' statement 'else' statement
   ;

whileStatement
   : (label=id ':')? 'while' '(' cond=expr ')'
      ('[' 'invariant' invariant=expr ']')?
      ('[' ('modifies'|'variant')   variant=ids ']')?
      statement
   ;

body
   : '{' statement* '}'
   ;

assignment
   : type? id ('[' aa=expr ']')? '=' rhs=expr ';'
   | type id ';' //declaraion
   ;

type
   : t=('double'|'float'|'int'|'bool') (a='[]')?
   ;

emptyStmt: ';';

assert_: 'assert' expr ';';
assume: 'assume' expr ';';
havoc: 'havoc' ids ';';
choose: 'choose' ids ':' expr ';';

returnStatement: 'return' expr ';';

statement
   : ifStatement
   | whileStatement
   | returnStatement
   | body
   | assignment
   | assert_
   | assume
   | havoc
   | choose
   | emptyStmt
   | procedureCall
   ;


typecast: '(' type ')' expr;
array_init: '{' (expr (',' expr)*)? '}';

expr
  :
    expr op=('*'|'/'|'%') expr
  | expr op=('+'|'-') expr
  | expr op=('<'|'<='|'>'|'>=') expr
  | expr op=('=='|'!=') expr
  | expr op='&&' expr
  | expr op='||' expr
  | expr op='^' expr
  | expr op='==>' expr
  | primary
  ;

primary
   :
     DOUBLE      #double
   | INT      #integer
   | BOOL      #bool
   | typecast #ignore2
   | array_init #ignore3
   | op=('!'|'-') expr #unary
   | '(' q=('\\forall'|'\\exists')  binders ';'  expr ')' #quantifiedExpr
   | '\\let'  type id '=' expr #letExpr
   | '(' expr ')' #parenExpr
   | id '(' exprList? ')' #fcall
   | id '[' exprList ']' #arrayaccess
   | id # ignore1
   ;

procedureCall: id '(' exprList? ')';

exprList: expr (',' expr)*;

id
   : IDENTIFIER
   ;

SL_COMMENT: '//' .*? '\n' -> skip;
ML_COMMENT: '/*' .*? '*/' -> skip;
VOID: 'void';

STRING
   : '"' ~["]* '"'
   ;

INT
   : [0-9] +
   ;

DOUBLE
   : INT* '.' INT
   ;

BOOL
   : 'true' | 'false'
   ;


IDENTIFIER
   : [a-zA-Z_] [a-zA-Z_0-9]*
   ;
WS
   : [ \r\n\t] -> skip
   ;