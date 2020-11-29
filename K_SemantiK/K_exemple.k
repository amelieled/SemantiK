module ARITH-SYNTAX
  imports DOMAINS

  syntax Aexp ::= Int
  	      	| Id
		| Aexp "*" Aexp [left]
		| Aexp "/" Aexp [left]
		| Aexp "+" Aexp [left] 
		| Aexp "-" Aexp [left]

endmodule

module ARITH
  imports ARITH-SYNTAX

  syntax KResult ::= Int

  configuration <T>
    <k> $PGM:K </k>
    <state> .Map </state>
  </T>

  rule N1:Int + N2:Int => N1 +Int N2
  rule N1:Int - N2:Int => N1 -Int N2
  rule N1:Int * N2:Int => N1 *Int N2
  rule N1:Int / N2:Int => N1 /Int N2 when N2 =/=Int 0

  context HOLE + _
  context _:Int + HOLE
  context HOLE - _
  context _:Int - HOLE
  context HOLE * _
  context _:Int * HOLE
  context HOLE / _
  context _:Int / HOLE

  rule <k> X:Id => N ...</k><state>... X |-> N ...</state>

endmodule

module BEXP-SYNTAX
  imports ARITH-SYNTAX

  syntax  Bexp ::= Bool // true and false
  	       | Aexp "<=" Aexp 
	       | Aexp "==" Aexp 
	       | "not" Bexp
	       |  Bexp "and" Bexp [left]
	       >  Bexp "or" Bexp [left]

endmodule

module BEXP
  imports BEXP-SYNTAX
  imports ARITH

  syntax KResult ::= Bool

  rule A1:Int <= A2:Int => A1 <=Int A2

  context HOLE <= _
  context _:Int <= HOLE

  rule A1:Int == A2:Int => A1 ==Int A2

  context HOLE == _
  context _:Int == HOLE

  rule not true => false
  rule not false => true

  context not HOLE

  rule true and B2 => B2
  rule false and B2 => false

  context HOLE and _

  rule true or _ => true
  rule false or B2 => B2

  context HOLE or _

endmodule

module IMP-SYNTAX
  imports BEXP-SYNTAX

  syntax CVal ::= "skip"
  syntax Com ::= CVal
             | Id ":=" Aexp
             | Com ";" Com [left]
             | "if" Bexp "then" Com "else" Com  
             | "while" Bexp "do" Com
             | "begin" Com "end"

endmodule

module IMP
  imports IMP-SYNTAX
  imports BEXP

  syntax KResult ::= CVal

  rule <k>X := A:Int => skip ...</k>
       <state>... X |-> (_ => A) ...</state>
  rule <k>X := A:Int => skip ...</k>
       <state> Rho:Map (.Map => X |-> A) </state>
          when notBool(X in keys(Rho))
  context X := HOLE

  rule skip ; C => C
  context HOLE ; _

  rule begin C end => C

  rule if true then C1 else _ => C1
  rule if false then _ else C2 => C2
  context if HOLE then _ else _

  rule while B do C =>
         if B then begin C ; while B do C end else skip

endmodule
