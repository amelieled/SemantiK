Require Import ZArith.
Require Import  ZArith_dec.

(* V type des noms des variables, on suppose que l'égalité est 
   décidable sur V*) 
Parameter V : Set.
Parameter eq_dec_V : forall (v1 v2:V),{v1=v2}+{~v1=v2}.

Inductive Exp : Set := 
Nb : Z -> Exp | Var : V -> Exp | Abs : V -> Exp -> Exp | App : Exp -> Exp -> Exp
|Plus : Exp -> Exp -> Exp .

(* type des valuations des variables et des fermetures *)
Inductive Val : Set :=  N : Z -> Val | Ferm : V -> Exp -> Sigma -> Val
with Sigma : Set := Env : (V -> Val) -> Sigma.

(* fonctions de manipulations des valuations*)
(*accès à une valeur*)
Definition valof : Sigma -> V -> Val :=
fun s => fun x => match s with (Env f) => f x end.

(* maj_val s x v : formalisation de s[x:=]*)
Definition newenv (s : Sigma) (x : V) (v : Val):=
      match s with 
      Env  f =>
      Env (fun (y:V) =>
           match eq_dec_V x y with
           | left _ => v
           | right _ => f y
           end)
      end.

(*formalisation de la sémantique big step des expressions de miniml*)
Inductive eval_Exp : Sigma -> Exp -> Val -> Prop :=
  eval_var : forall (s:Sigma)(v : V),(eval_Exp s (Var v) (valof s v))
| eval_nb :  forall (s:Sigma)(n : Z), (eval_Exp s (Nb n) (N n))
| eval_plus : forall (s : Sigma)(a1 a2 : Exp) (v w : Z),
    (eval_Exp s a1 (N v)) ->
    (eval_Exp s a2 (N w)) ->
    (eval_Exp s (Plus a1 a2) (N (v+w)))
| eval_abst: forall (s:Sigma)(a:Exp)(x : V),
    (eval_Exp s (Abs x a) (Ferm x a s))
| eval_app : forall (s s1 : Sigma)(a a1 a2 : Exp)(x:V) (v w : Val),
    (eval_Exp s a1 (Ferm x a s1)) -> 
    (eval_Exp s a2 v) ->
    (eval_Exp (newenv s1 x v) a w) ->
    (eval_Exp s (App a1 a2) w).

(* le langage est déterministe*)
Lemma Exp_deterministe : forall (e : Exp)(s : Sigma)(n1 : Val),
(eval_Exp s e n1) -> forall (n2 : Val),(eval_Exp s e n2) -> n1=n2.
(*A compléter.*)