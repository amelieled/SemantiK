
Inductive Exp : Set := 
 | constante : nat -> Exp
 | variable  : Exp
 | plus      : Exp -> Exp -> Exp
 | mult      : Exp -> Exp -> Exp
 | egal      : Exp -> Exp -> Exp
 | not       : Exp -> Exp
 | and       : Exp -> Exp -> Exp.