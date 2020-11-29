Require Import ZArith.
Require Import ZArith_dec.

(* V type des noms des variables, on suppose que l'\u00e9galit\u00e9 est 
   d\u00e9cidable sur V*) 
Definition V := nat.

Parameter eq_dec_V : forall (v1 v2:V),{v1=v2}+{~v1=v2}.

Inductive Exp : Set := 
Nb : Z -> Exp | Var : V -> Exp | Abs : V -> Exp -> Exp | App : Exp -> Exp -> Exp
|Plus : Exp -> Exp -> Exp | Letin : V -> Exp -> Exp -> Exp | Unit.

(* type des valuations des variables et des fermetures *)
Inductive Val : Set :=  N : Z -> Val | Ferm : Exp -> Sigma -> Val
with Sigma : Set := Env : (V -> Val) -> Sigma.

(* fonctions de manipulations des valuations*)
(*acc\u00e8s \u00e0 une valeur*)
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


Fixpoint max (x y:V) {struct x} : V :=
  match x, y with
    | 0, _ => y
    | S n, 0 => x
    | S n, S m => S (max n m)
  end.

Fixpoint newvar (e:Exp) : V := match e with
  | Var i => i+1
  | Abs _ e2 => newvar e2
  | App e1 e2 => max (newvar e1) (newvar e2)
  | Plus e1 e2=> max (newvar e1) (newvar e2)
  | Letin _ e1 e2=> max (newvar e1) (newvar e2)
  | _ => 0
end.

(*formalisation de la s\u00e9mantique big step appel par valeur des expressions de miniml*)
Inductive eval_Exp : Sigma -> Exp -> Val -> Prop :=
  eval_var : forall (s:Sigma)(v : V),(eval_Exp s (Var v) (valof s v))
| eval_nb :  forall (s:Sigma)(n : Z), (eval_Exp s (Nb n) (N n))
| eval_plus : forall (s : Sigma)(a1 a2 : Exp) (v w : Z),
    (eval_Exp s a1 (N v)) ->
    (eval_Exp s a2 (N w)) ->
    (eval_Exp s (Plus a1 a2) (N (v+w)))
| eval_abst: forall (s:Sigma)(a:Exp)(x : V),
    (eval_Exp s (Abs x a) (Ferm (Abs x a) s))
| eval_app : forall (s s1 : Sigma)(a a1 a2 : Exp)(x:V) (v w : Val),
    (eval_Exp s a1 (Ferm (Abs  x a) s1)) -> 
    (eval_Exp s a2 v) ->
    (eval_Exp (newenv s1 x v) a w) ->
    (eval_Exp s (App a1 a2) w)
| eval_letin : forall (s:Sigma)(a e:Exp)(x:V)(v v1:Val), 
    (eval_Exp s a v1 ) ->
    (eval_Exp (newenv s x v1) e v ) ->
    (eval_Exp s (Letin x a e) v).

Definition equiv (e1 e2:Exp) : Prop :=
  forall (s:Sigma)(v:Val),
  (eval_Exp s e1 v) <->
  (eval_Exp s e2 v).

Lemma equiv_ex : forall(e1 e2:Exp)(x:V), 
  equiv (Letin x e1 e2) (App (Abs x e2) e1).
Proof.
intros e1 e2 v.
unfold equiv.
intros s v0.
split.
intro H.
inversion H.
eapply eval_app.
apply eval_abst.
apply H5.
apply H6.
intro H.
inversion H.
eapply eval_letin.
apply H4.
inversion H2.
apply H6.
Qed.

(*  QUESTION 6  *)
(*formalisation de la s\u00e9mantique big step appel par nom des expressions de miniml*)
Inductive evaln_Exp : Sigma -> Exp -> Val -> Prop :=
  evaln_var : forall (s s1:Sigma)(x:Exp)(z:Z)(v : V),
  (valof s v) = N z ->
  (evaln_Exp s (Var v) (N z))
| evaln_var2 : forall (s s1:Sigma)(x:Exp)(val:Val)(v : V),
  (valof s v) = Ferm x s1 ->
  (evaln_Exp s1 x val) ->
  (evaln_Exp s (Var v) val)
| evaln_nb :  forall (s:Sigma)(n : Z), (evaln_Exp s (Nb n) (N n))
| evaln_plus : forall (s : Sigma)(a1 a2 : Exp) (v w : Z),
    (evaln_Exp s a1 (N v)) ->
    (evaln_Exp s a2 (N w)) ->
    (evaln_Exp s (Plus a1 a2) (N (v+w)))
| evaln_abst: forall (s:Sigma)(a:Exp)(x : V),
    (evaln_Exp s (Abs x a) (Ferm (Abs x a) s))
| evaln_app : forall (s s1 : Sigma)(a a1 a2 : Exp)(x:V) (v w : Val),
    (evaln_Exp s a1 (Ferm (Abs  x a) s1)) -> 
    (evaln_Exp s a2 v) ->
    (evaln_Exp (newenv s1 x v) a w) ->
    (evaln_Exp s (App a1 a2) w)
| evaln_letin : forall (s:Sigma)(a e:Exp)(x:V)(v v1:Val), 
    (evaln_Exp s a v1 ) ->
    (evaln_Exp (newenv s x v1) e v ) ->
    (evaln_Exp s (Letin x a e) v).


(*  QUESTION 8  *)

Definition equivn (e1 e2:Exp) : Prop :=
  forall (s:Sigma)(v:Val),
  (evaln_Exp s e1 v) <->
  (evaln_Exp s e2 v).


Lemma equivn_ex : forall(e1 e2:Exp)(x:V), 
  equivn (Letin x e1 e2) (App (Abs x e2) e1).
Proof.
intros e1 e2 x.
unfold equivn.
intros s v.
split; intro H.
inversion H.
eapply evaln_app.
apply evaln_abst.
apply H5.
apply H6.
(* si on fait l'inversion apr\u00e8s le eapply *)
inversion H.
eapply evaln_letin.
(* erreur interne de coq !! lors du apply H4 *)
apply H4.
inversion H2.
apply H6.
Qed.

(*  QUESTION 12  *)

Fixpoint lf_to_lfu (e:Exp) : Exp := match e with
    Nb n => Nb n
  | Var x => App (Var x) Unit
  | Abs x e1 => Abs x (lf_to_lfu e1)
  | App e1 e2   => App (lf_to_lfu e1) (Abs (newvar e)(lf_to_lfu e2))
  | Plus e1 e2  => Plus (lf_to_lfu e1)(lf_to_lfu e2)
  | Letin x e1 e2 => Letin x (Abs(newvar e)(lf_to_lfu e1)) (lf_to_lfu e2)
  | _ => e
end.

(*Load "typage.v".*)
Require Import Typage.

(*  QUESTION 13  *)

Lemma verif_type_q13_1 : forall (s:typenv),
  estbientype s (App (Abs 1 (Nb 3)) (Plus (Nb 1)(Nb 2))) TInt.
Proof.
intro s.
eapply type_app.
apply s.
assert (estbientype s (Abs 1 (Nb 3))(TArrow TInt TInt)).
apply type_abst.
apply type_nb.
apply H.
apply type_plus.
apply type_nb.
apply type_nb.
Qed.


Lemma typinnewtypenv : forall (s:typenv)(v:V)(t:typ),
  ((typof (newtypenv s v t) v) = t).
Proof.
intros s v t.
unfold typof.
unfold newtypenv.
compute.
destruct (eq_dec_V v v).
reflexivity.
absurd (v<>v).
unfold not.
intro H.
apply H.
reflexivity.
apply n.
Qed.

Lemma typofVar : forall (s:typenv)(x:V)(t:typ),
  estbientype (newtypenv s x t) (Var x) t.
intros s x t.
assert (estbientype (newtypenv s x t) (Var x) (typof (newtypenv s x t) x)).
apply type_var.
assert (t = typof (newtypenv s x t) x).
symmetry.
apply typinnewtypenv.
rewrite H0.
assert (newtypenv s x (typof (newtypenv s x t) x) = newtypenv s x t).
symmetry in H0.
rewrite H0.
reflexivity.
rewrite H1.
apply type_var.
Qed.



Lemma verif_type_q13_2 : forall (s:typenv),
  estbientype s (App (Abs 1 (Plus (Var 1)(Var 1))) (Plus (Nb 1)(Nb 2))) TInt.
Proof.
intro s.
eapply type_app.
apply s.
apply type_abst.
assert (estbientype (newtypenv s 1 TInt) (Plus (Var 1) (Var 1)) TInt).
apply type_plus.
apply typofVar.
apply typofVar.
apply type_plus.
apply typofVar.
apply typofVar.
apply type_plus.
apply type_nb.
apply type_nb.
Qed.


(*  QUESTION 14  *)


Lemma verif_type_q14_1 : forall (s:typenv),
  estbientype s (lf_to_lfu (App (Abs 1 (Nb 3)) (Plus (Nb 1)(Nb 2)))) TInt.
Proof.
intro s.
simpl.
eapply type_app.
apply s.
apply type_abst.
apply type_nb.
apply type_abst.
apply type_plus.
assert (estbientype (newtypenv s 0 TUnit) (Nb 1) TInt).
apply type_nb.
apply H.
apply type_nb.
Qed.


Lemma verif_type_q14_2 : forall (s:typenv),
  estbientype s (lf_to_lfu (App (Abs 1 (Plus (Var 1)(Var 1))) (Plus (Nb 1)(Nb 2)))) TInt.
Proof.
intro s.
simpl.
eapply type_app.
apply s.
apply type_abst.
assert(estbientype (newtypenv s 1 (TArrow TUnit TInt)) (Plus (App (Var 1) Unit) (App (Var 1) Unit))  TInt).
apply type_plus; eapply type_app.
apply s.
apply typofVar.
apply type_unit.
apply s.
apply typofVar.
apply type_unit.
apply type_plus; eapply type_app.
apply s.
apply typofVar.
apply type_unit.
apply s.
apply typofVar.
apply type_unit.
apply type_abst.
apply type_plus; apply type_nb.
Qed.


(*  QUESTION 15  *)

Fixpoint typlf_to_lfu (t:typ) : typ := match t with
| TInt => TInt
| TArrow t1 t2 => TArrow (TArrow TUnit (typlf_to_lfu t1)) (typlf_to_lfu t2)
| _ => t
end.

Definition typenvlf_to_lfu (s:typenv)(v:V) : typ := match v with
| v => typlf_to_lfu (s v)
end.


Lemma trans_typ : forall (s:typenv)(e:Exp)(t:typ),
  estbientype s e t -> estbientype (typenvlf_to_lfu s) (lf_to_lfu e) (typlf_to_lfu t).
Proof.
intros s e t.
intro H.
induction e; simpl.
inversion H.
simpl.
apply type_nb.
inversion H.
rewrite H1.
eapply type_app.
apply s.
assert (TArrow TUnit (typlf_to_lfu t) = typof (typenvlf_to_lfu s) v).
unfold typof.
unfold typenvlf_to_lfu.
unfold typlf_to_lfu.


