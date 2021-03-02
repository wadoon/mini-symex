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

grammar tinyc;

program: procedure+;

procedure
   : (type|'void') name=id '(' a=binders?  ')'
       ('[' 'pre'        pre=expr ']')?
       ('[' 'post'       post=expr ']')?
       ('[' 'modifies'   modifies=ids ']')?
      body
   ;

binders: type id (',' type id)*;
ids: id (',' type id)*;


ifStatement
   : 'if' '(' expr ')' statement
   | 'if' '(' expr ')' statement 'else' statement
   ;

whileStatement
   : 'while' '(' cond=expr ')'
      ('[' 'invariant' invariant=expr ']')?
      ('[' ('modifies'|'variant')   variant=ids ']')?
      statement
   ;

body
   : '{' statement* '}'
   ;

assignment
   : type? id ('[' aa=expr ']')? '=' rhs=expr ';'
   ;

type
   : t=('int'|'bool') (a='[]')?
   ;

emptyStmt: ';';

assert_: 'assert' expr ';';
assume: 'assume' expr ';';
havoc: 'havoc' ids ';';

statement
   : ifStatement
   | whileStatement
//   | 'do' statement 'while' paren_expr ';'
   | body
   | assignment
   | assert_
   | assume
   | havoc
   | emptyStmt
   ;

expr
  : expr op=('+'|'-') expr
  | expr op=('*'|'/'|'%') expr
  | expr op='&' expr
  | expr op='|' expr
  | expr op='^' expr
  | expr op=('<'|'<='|'>'|'>=') expr
  | expr op=('=='|'!=') expr
  | primary
  ;

primary
   : id           # ignore1
   | INT      #integer
   | BOOL      #bool
   | '(' q=('\\forall'|'\\exists')  binders ';'  expr ')' #quantifiedExpr
   | '\\let'  type id '=' expr #letExpr
   | '(' expr ')' #parenExpr
   | id '(' expr (',' expr)* ')' #fcall
   | id '[' expr ']' #arrayaccess
   ;

id
   : IDENTIFIER
   ;

STRING
   : '"' ~["]* '"'
   ;

INT
   : [0-9] +
   ;

BOOL
   : 'true' | 'false'
   ;


IDENTIFIER
   : [a-z]+
   ;

WS
   : [ \r\n\t] -> skip
   ;