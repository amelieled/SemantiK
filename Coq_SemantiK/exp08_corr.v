    Require Import ZArith.
    Require Import ZArith_dec.
    Require Import Zdiv.
    Require Import Bool.
    Require Import List.

   (* V type des noms des variables, on suppose que l'égalité est 
      décidable sur V*) 
    Parameter V : Set.

    Parameter eq_dec_V : forall v1 v2 : V, {v1 = v2} + {v1 <> v2}.

    Inductive Exp : Set :=
      | nb : Z -> Exp
      | var : V -> Exp
      | pls : Exp -> Exp -> Exp
      | egal : Exp -> Exp -> Exp 
      | neg : Exp -> Exp 
      | et : Exp -> Exp -> Exp .

(* type des valuations des variables = environnements*)
    Definition Sigma : Set := V -> Z.

(* eval_Exp s e v : formalisation Coq de <e,s> -> v*) 

    Definition Znegate (n : Z) : Z :=
    match (Z.eq_dec n 0) with
       left _ =>  1%Z 
    |  right _ => 0%Z
    end. 

    Definition Zegal (n1 n2 : Z) : Z :=
    match (Z.eq_dec n1 n2) with
       left _ =>  0%Z 
    |  right _ => 1%Z
    end. 

    Inductive eval_Exp : Sigma -> Exp -> Z -> Prop :=
      | eval_var : forall (s : Sigma) (v : V), eval_Exp s (var v) (s v)
      | eval_nb : forall (s : Sigma) (n : Z), eval_Exp s (nb n) n
      | eval_pls :
          forall (s : Sigma) (a1 a2 : Exp) (n1 n2 : Z),
          eval_Exp s a1 n1 ->
          eval_Exp s a2 n2 -> eval_Exp s (pls a1 a2) (n1 + n2)%Z
      | eval_egal :
          forall (s : Sigma) (a1 a2 : Exp) (n1 n2 : Z),
          eval_Exp s a1 n1 -> eval_Exp s a2 n2 ->
            eval_Exp s (egal a1 a2) (Zegal n1 n2)
      | eval_et :
          forall (s : Sigma) (a1 a2 : Exp) (n1 n2 : Z),
          eval_Exp s a1 n1 ->
          eval_Exp s a2 n2 -> eval_Exp s (et a1 a2) (n1 * n2)%Z
      | eval_neg :
          forall (s : Sigma) (e : Exp) (n : Z),
          eval_Exp s e n -> eval_Exp s (neg e) (Znegate n).

(* le langage des expressions est déterministe*)
    Lemma Exp_deterministe :
     forall (e : Exp) (s : Sigma) (n1 n2 : Z),
     eval_Exp s e n1 -> eval_Exp s e n2 -> n1 = n2.
Proof.
(* à compléter*)
induction e.
(*nb*)
   intros.
   inversion H.
   inversion H0.
   intuition.
(*var*)
   intros.
   inversion H.
   inversion H0.
   trivial.
(*plus*)
   intros.
   inversion H.
   inversion H0.
   assert (n0=n4).
   apply (IHe1 s n0 n4);assumption.
   assert (n3=n5).
   apply (IHe2 s n3 n5);assumption.
   intuition.
(*egal*)
   intros.
   inversion H.
   inversion H0.
   assert (n0 = n4).
  apply (IHe1 s n0 n4); assumption.
  assert (n3 = n5).
   apply (IHe2 s n3 n5); assumption.
   rewrite H13.
     rewrite H14.
     trivial.
(*neg*) 
     intros.
   inversion H.
   inversion H0.
  assert (n = n0).
   apply (IHe s n n0); assumption.
   rewrite H9;trivial.
(*et*)
   intros.
   inversion H.
   inversion H0.
   assert (n0 = n4).
  apply (IHe1 s n0 n4); assumption.
  assert (n3 = n5).
   apply (IHe2 s n3 n5); assumption.
   rewrite H13.
     rewrite H14.
     trivial.
Qed.