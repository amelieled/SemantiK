// SEMANTIQUE OPERATIONNELLE

require open amelie.lambdapi_examples.Notation
require open amelie.lambdapi_examples.Nat
require open amelie.lambdapi_examples.Bool
require open amelie.lambdapi_examples.Operations

symbol if {a} : 𝔹 → a → a → a
rule if true  $t _  ↪ $t
with if false _  $f ↪ $f

symbol substraction : ℕ → ℕ → ℕ
set infix left 6 "-" ≔ substraction
rule       0 - $y ↪ 0
with      $y - 0  ↪ 0
with succ $x - succ $y ↪ $x - $y

symbol division : ℕ → ℕ → ℕ
set infix left 6 "÷" ≔ division
rule       0 ÷ _ ↪ 0
//with succ $x + $y ↪ succ ($x + $y)

// EXPRESSIONS ARITHMETIQUES

// OCaml
// type ’a exp_arith =
//     Ent of int | Var of ’a
//   | Plus of ’a exp_arith*’a exp_arith
//   | Moins of ’a exp_arith*’a exp_arith
//   | Fois of ’a exp_arith*’a exp_arith
//   | Div of ’a exp_arith*’a exp_arith;;
constant symbol EA : Set → Set
set declared "𝔼𝔸"
definition 𝔼𝔸a ≔ τ (EA a)
constant symbol ent {a} : ℕ → 𝔼𝔸a
constant symbol var {a} : τ a → 𝔼𝔸a
constant symbol plus {a} : 𝔼𝔸a → 𝔼𝔸a → 𝔼𝔸a
constant symbol moins {a} : 𝔼𝔸a → 𝔼𝔸a → 𝔼𝔸a
constant symbol fois {a} : 𝔼𝔸a → 𝔼𝔸a → 𝔼𝔸a
constant symbol div {a} : 𝔼𝔸a → 𝔼𝔸a → 𝔼𝔸a
symbol EA_ind {a} (p : 𝔼𝔸a → Prop) :
(Πn, π (p (ent n))) →
(Πx, π (p (var x))) →
(Πa1, π (p a1) → Πa2, π (p a2) → π (p (plus a1 a2))) →
(Πa1, π (p a1) → Πa2, π (p a2) → π (p (moins a1 a2))) →
(Πa1, π (p a1) → Πa2, π (p a2) → π (p (fois a1 a2))) →
(Πa1, π (p a1) → Πa2, π (p a2) → π (p (div a1 a2))) →
Πx, π (p x)

// INTERPRETATION des EXPR. ARITH

//Inductive values : Set := Val : Z -> values | Erreur : values.
constant symbol values : Set
set declared "𝕍"
definition 𝕍 ≔ τ values
constant symbol val : ℕ → 𝕍
constant symbol erreur : 𝕍

// INTERPRETATION des SYMBOLES

symbol i_plus : 𝕍→ 𝕍→ 𝕍
rule i_plus (val $n1) (val $n2) ↪ val ($n1 + $n2)
with i_plus erreur _ ↪ erreur
with i_plus _ erreur ↪ erreur

symbol i_moins: 𝕍→ 𝕍→ 𝕍
rule i_moins (val $n1) (val $n2) ↪ val ($n1 - $n2)
with i_moins erreur _ ↪ erreur
with i_moins _ erreur ↪ erreur

symbol i_fois : 𝕍→ 𝕍→ 𝕍
rule i_fois (val $n1) (val $n2) ↪ val ($n1 × $n2)
with i_fois erreur _ ↪ erreur
with i_fois _ erreur ↪ erreur

symbol i_div : 𝕍→ 𝕍→ 𝕍
rule i_div (val $n1) (val $n2) ↪
    if (eqb_nat $n2 0) erreur (val ($n1 ÷ $n2))
with i_div erreur _ ↪ erreur
with i_div _ erreur ↪ erreur

// EVALUATION des EXPR. ARITH

// Definition Sigma : Set := V -> Z.
constant symbol sigma : Set
//set declared "Σi"
//definition Σi ≔ 𝕍→ ℕ
set declared "Σ"
definition Σ {a} ≔ τ a → ℕ

//Fixpoint eval_EA_fct (s:Sigma)(a:EA){struct a} : values :=
// match a with
// (nb n) => (Val n)
// | (var x) => (Val (s x))
// | ...
// | (dv a1 a2) => match ((eval_EA_fct s a1),(eval_EA_fct s a2)) with
// ((Val n1),(Val n2)) => (match n2 with
// ‘0‘ => Erreur
// | _ => (Val (Zdiv n1 n2))
// end)
// | (Erreur,_) => Erreur
// | ((Val _), Erreur) => Erreur
// end)
// end.
symbol eval_EA_fct {a} : Σ {a} → 𝔼𝔸a → 𝕍
rule eval_EA_fct _ (ent $n) ↪ val $n
with eval_EA_fct $s (var $x) ↪ val ($s $x)
with eval_EA_fct $s (plus $a1 $a2)  ↪
     i_plus  (eval_EA_fct $s $a1) (eval_EA_fct $s $a2)
with eval_EA_fct $s (moins $a1 $a2) ↪
     i_moins (eval_EA_fct $s $a1) (eval_EA_fct $s $a2)
with eval_EA_fct $s (fois $a1 $a2)      ↪
     i_fois  (eval_EA_fct $s $a1) (eval_EA_fct $s $a2)
with eval_EA_fct $s (div$a1 $a2)    ↪
     i_div   (eval_EA_fct $s $a1) (eval_EA_fct $s $a2)

compute eval_EA_fct _ (plus (ent 3) (ent 4))

// SEMANTIQUE OPERATIONNELLE D'EVALUATION A GRANDS PAS

// Inductive eval_EA : EA -> Sigma -> values -> Prop :=
// | eval_var : forall (s:Sigma)(v:V),(eval_EA (var v) s (s v))
// | eval_nb : forall (s:Sigma)(n : Z), (eval_EA (nb n) s (Val n))
// | eval_pls : forall (s:Sigma)(a1 a2:EA)(n1 n2:values),
// (eval_EA a1 s n1) -> (eval_EA a2 s n2) ->
// (eval_EA (pls a1 a2) s (ZplusErr n1 n2))
// ...
// | eval_dv : forall (s:Sigma)(a1 a2:EA)(n1 n2: values),
// (eval_EA s a1 n1) -> (eval_EA s a2 n2) ->
// (eval_EA s (dv a1 a2) (ZdivErr n1 n2)).
// avec Definition ZplusErr (v1 v2 : values) : values := match (v1, v2) with
// Val x1, Val x2 => Val (x1 + x2)
// | Erreur, _ => Erreur
// | _, Erreur => Erreur
// end.
symbol eval_EA {a} : 𝔼𝔸a → Σ {a} → 𝕍→ Prop
constant symbol eval_var {a} (s:Σ {a}) x :
  π (eval_EA (var x) s (val (s x)))
constant symbol eval_nb  {a} (s:Σ {a}) n :
  π (eval_EA (ent n) s (val n))
constant symbol eval_plus {a} (s:Σ {a}) a1 a2 n1 n2 :
  π (eval_EA a1 s n1) → π (eval_EA a2 s n2) →
  π (eval_EA (plus a1 a2) s (i_plus n1 n2))
// constant symbol eval {a} (s:Σ {a}) a1 a2 n1 n2 :
//  π (eval_EA s (plus a1 a2) (i_plus  (eval_EA s a1) (eval_EA s a2)))
constant symbol eval_moins {a} (s:Σ {a}) a1 a2 n1 n2 :
  π (eval_EA a1 s n1) → π (eval_EA a2 s n2) →
  π (eval_EA (moins a1 a2) s (i_moins n1 n2))
constant symbol eval_fois {a} (s:Σ {a}) a1 a2 n1 n2 :
  π (eval_EA a1 s n1) → π (eval_EA a2 s n2) →
  π (eval_EA (fois a1 a2) s (i_fois n1 n2))
constant symbol eval_div {a} (s:Σ {a}) a1 a2 n1 n2 :
  π (eval_EA a1 s n1) → π (eval_EA a2 s n2) →
  π (eval_EA (div a1 a2) s (i_div n1 n2))

//compute eval_EA (plus (ent 3) (ent 4)) _ (val (ent 7))
theorem eval_example (s:Σ {nat}) :
π (eval_EA {nat} (fois {nat} (ent {nat} 2) (ent {nat} 3)) s (val 6))
//π (eval_EA (ent 2) s (val (ent 5)))
proof
  assume s
  refine eval_fois s _ _ _ _
qed

theorem det_eval_EA {t} a (s:Σ {t}) v1 v2 :
π (eval_EA a s v1) → π (eval_EA a s v2) → π (v1 = v2)
proof
  //assume t a s v1 v2
  refine EA_ind _ _ _ _ _ _ //t a s v1 v2
qed
