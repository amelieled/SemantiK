(* le typage monomorphe *)
(* A ajouter à la suite de votre fichier coq*)
Require Import Exp.

Variable VarTyp : Set.

Inductive typ : Set :=
  TVar : VarTyp -> typ
| TArrow : typ -> typ -> typ 
| TInt : typ
| TUnit : typ.


Definition typenv  := V -> typ.

Definition typof : typenv -> V -> typ :=
fun s => fun x => s x.

(* maj_val s x v : formalisation de s[x:=]*)
Definition newtypenv (s : typenv) (x : V) (v : typ):=
fun y =>
           match eq_dec_V x y with
           | left _ => v
           | right _ => s y
           end.

Inductive estbientype : typenv -> Exp -> typ -> Prop :=
  type_var : forall (s:typenv)(v : V),(estbientype s (Var v) (typof s v))
| type_nb :  forall (s:typenv)(n : Z) ,(estbientype s (Nb n) TInt)
| type_unit :  forall (s:typenv), (estbientype s Unit TUnit)
| type_plus : forall (s : typenv)(a1 a2 : Exp),
    (estbientype s a1 TInt) ->
    (estbientype s a2 TInt) ->
    (estbientype s (Plus a1 a2) TInt)
| type_abst: forall (s:typenv)(a:Exp)(x : V)(t1 t2 : typ),
      (estbientype (newtypenv s x t1) a t2) ->
          (estbientype s (Abs x a) (TArrow t1 t2))
| type_app : forall (s s1 : typenv)(a1 a2 : Exp)(t1 t2 : typ),
    (estbientype s a1 (TArrow t1 t2)) -> 
    (estbientype s a2 t1) ->
    (estbientype s (App a1 a2) t2).