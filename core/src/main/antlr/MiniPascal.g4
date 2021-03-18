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

grammar MiniPascal;

program: (procedure|function)+;

procedure
   : PROCEDURE name=id '(' a=binders?  ')' ';'?
      var
      spec
      body
   ;


function
   : FUNCTION name=id '(' a=binders?  ')' ':' type ';'?
      var
      spec
      body
   ;

var: 'var' (varDecl (';' varDecl)* ';'?)?;
varDecl: ids ':' type (':=' rhs=expr)?;

namedexpr: (id ':')? expr;
namedexprs: namedexpr ((';') namedexpr)*;
spec:
      ('pre'      pre=namedexprs)?
      ('post'     post=namedexprs)?
      ('modifies' modifies=ids)?
    ;

binders: id ':' type  (','  id ':' type)*;
ids: id (',' id)*;

ifStatement
   : 'if' expr 'then' statement
   | 'if' expr 'then' statement 'else' statement
   ;

whileStatement
   : 'while' cond=expr
      loopSpec
      'do'
      statement
   ;

loopSpec
    :  (INVARIANT        invariant=namedexprs)?
       ((MODIFIES|VARIANT) variant=ids)?
    ;

body
    : BEGIN statement (';' statement)* ';'? END
    ;

assignment
   : id ('[' aa=expr ']')? ASSIGN rhs=expr
   ;

primitiveTypes: 'int'|'bool';

type
   : t=primitiveTypes (a=LBRACKET RBRACKET)?
   | 'array' 'of' primitiveTypes
   ;


emptyStmt: ';';

assert_: ASSERT ( '(' namedexprs ')' | namedexprs);
assume:  ASSUME ( '(' namedexprs ')' | namedexprs);
havoc:   HAVOC  ( '(' ids ')' | ids);


statement
   : ifStatement
   | whileStatement
   | body
   | assignment
   | assert_
   | assume
   | havoc
   ;

expr
  : expr op=(PLUS|MINUS) expr
  | expr op=(MUL|DIV|MOD) expr
  | expr op=AND expr
  | expr op=OR expr
  | expr op=XOR expr
  | expr op=(LT|LTE|GTE|GT) expr
  | expr op=(EQUAL|NOT_EQUAL) expr
  | expr op=IMPL expr
  | primary
  ;

primary
   : id       #ignore1
   | INT_LITERAL      #integer
   | BOOL_LITERAL     #bool
   | op=('!'|'-') expr #unary
   | '(' q=('\\forall'|'\\exists')  binders ';'  expr ')' #quantifiedExpr
   | '\\let'  type id '=' expr #letExpr
   | '(' expr ')' #parenExpr
   | id '(' exprList ')' #fcall
   | id '[' exprList ']' #arrayaccess
   ;

exprList: expr (',' expr)*;

PROCEDURE: 'procedure';
FUNCTION: 'function';
VAR: 'var';
COMMA: ',';
BANG:'!';
FORALL:'\\forall';
EXISTS:'\\exists';
SEMI: ';';
COLON:':';
MINUS:'-';
ARRAY: 'array';
OF: 'of';
IMPL:'==>';
EQUAL:'=';
NOT_EQUAL:'<>';
LT:'<';
GT:'>';
LTE:'<=';
GTE:'>=';
MOD:'%' | 'mod';
OR:'||' | 'or';
AND:'&&' | 'and';
ASSIGN:':=';
LET: '\\let';
LPAREN:'(';
RPAREN:')';
LBRACKET:'[';
RBRACKET:']';
PLUS:'+';
XOR:'^';
MUL:'*';
DIV:'/';
INVARIANT:'invariant';
MODIFIES:'modifies';
VARIANT:'variant';
BEGIN:'begin';
END:'end';
PRE:'pre';
POST:'post';
WHILE:'while';
DO:'do';
IF:'if';
THEN:'then';
ELSE: 'else';
INT: 'int';
BOOL: 'bool';
HAVOC: 'havoc';
ASSUME: 'assume';
ASSERT: 'assert';

id
   : IDENTIFIER
   ;



STRING_LITERAL
   : '"' ~["]* '"'
   ;

INT_LITERAL
   : [0-9] +
   ;

BOOL_LITERAL
   : 'true' | 'false'
   ;

IDENTIFIER
   : [a-zA-Z_]+
   ;

BLOCK_COMMENT
   : '(*' (BLOCK_COMMENT|.)*? '*)' -> channel(HIDDEN)
   ;

LINE_COMMENT
   : '//' ~([\n\r]) [\n\r] -> channel(HIDDEN)
   ;


WS
   : [ \r\n\t] -> channel(HIDDEN)
   ;