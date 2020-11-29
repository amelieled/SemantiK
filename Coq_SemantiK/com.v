Require Import ZArith.
Require Import ZArith_dec.
Require Import Zdiv.
Require Import Bool.
Require Import List.

Require Import exp.

    (***************************************
             Langage impératif
    ****************************************)
    
(* maj_val s x v : formalisation de s[x<-v]*)
   Definition maj_val (s : Sigma) (x : V) (v : Z) (y : V) :=
      match eq_dec_V x y with
      | left _ => v
      | right _ => s y
      end.

   Lemma maj1 : forall (s : Sigma) (x : V) (v : Z) (y : V), 
   x<>y -> (maj_val s x v) y = s y.
intros.
unfold maj_val in |- *.
elim (eq_dec_V x y).
 intro.
   absurd (x = y); assumption.
 auto.
Qed.

   Lemma maj2 : forall (s : Sigma) (x : V) (v : Z) ,
   (maj_val s x v) x = v.
intros.
unfold maj_val.
elim (eq_dec_V x x);intro.
auto.
   absurd (x = x); auto.
Qed.

(* syntaxe abstraite des commandes*)
   Inductive com : Set :=
      | aff : V -> Exp -> com        (*affectation*)
      | seq : com -> com -> com      (* séquence*)
      | repeat : Exp -> com -> com.  (* boucle repeat*)

 (* exec_com s c s' : formalisation de <c, s> -> s', 
   sémantique Big Step des commandes*)
   Inductive exec_com : Sigma -> com -> Sigma -> Prop :=
      | exec_aff :
          forall (s : Sigma) (e : Exp) (n : Z) (x : V),
          eval_Exp s e n -> exec_com s (aff x e) (maj_val s x n)
      | exec_seq :
          forall (s s1 s2 : Sigma) (c1 c2 : com),
          exec_com s c1 s1 -> exec_com s1 c2 s2 -> exec_com s (seq c1 c2) s2
      | exec_repeat_t :
          forall (s s1 : Sigma) (n : Z) (b : Exp) (c : com),
          exec_com s c s1 ->
          eval_Exp s1 b n -> n <> 0%Z -> exec_com s (repeat b c) s1
      | exec_repeat_f :
          forall (s s1 s2 : Sigma) (b : Exp) (c : com),
          exec_com s c s1 ->
          eval_Exp s1 b 0%Z ->
          exec_com s1 (repeat b c) s2 -> exec_com s (repeat b c) s2.

(*le langage des commandes est déterministe*)
    Lemma com_deterministe :
     forall (c : com) (s s1 : Sigma),
     exec_com s c s1 -> forall s2 : Sigma, exec_com s c s2 -> s1 = s2.
