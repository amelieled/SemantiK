    Require Import ZArith.
    Require Import ZArith_dec.
    Require Import Zdiv.
    Require Import Bool.
    Require Import List.

(* V type des noms des variables, on suppose que l'égalité est 
   décidable sur V*) 
Parameter V : Set.
Parameter eq_dec_V : forall (v1 v2:V), {v1=v2}+{~v1=v2}.

Inductive Exp : Set := 
nb : Z -> Exp | var : V -> Exp | pls : Exp -> Exp -> Exp |
mlt : Exp -> Exp -> Exp | opp : Exp -> Exp.

(* type des valuations des variables*)
Definition Sigma : Set := V -> Z. 

(*formalisation de la sémantique big step des expressions arithmétiques*)
Inductive eval_Exp : Sigma -> Exp -> Z -> Prop :=
  eval_var (s:Sigma) (v:V) : (eval_Exp s (var v) (s v))
| eval_nb  (s:Sigma) (n:Z) : (eval_Exp s (nb n) n)
| eval_pls (s:Sigma) (a1 a2:Exp) (n1 n2:Z) : 
 (eval_Exp s a1 n1) -> (eval_Exp s a2 n2) ->
    (eval_Exp s (pls a1 a2) (n1+n2))
| eval_mlt (s:Sigma)(a1 a2:Exp) (n1 n2:Z) :
 (eval_Exp s a1 n1) -> (eval_Exp s a2 n2) ->
    (eval_Exp s (mlt a1 a2) (n1*n2))
| eval_opp (s:Sigma)(a1 :Exp) (n1:Z) :
 (eval_Exp s a1 n1) -> (eval_Exp s (opp a1) (-n1)).

(* le langage est déterministe*)
Lemma Exp_deterministe : forall (e : Exp) (s : Sigma) (n1 n2 : Z),
(eval_Exp s e n1) -> (eval_Exp s e n2) -> n1=n2.
Proof.
Admitted.
(*A compléter.*)