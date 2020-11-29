// SEMANTIQUE OPERATIONNELLE

require open amelie.lambdapi_examples.Notation
require open amelie.lambdapi_examples.Nat
require open amelie.lambdapi_examples.Bool
require open amelie.lambdapi_examples.Operations
require open amelie.lambdapi_examples.Constructive_logic

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

// Coq
// Parameter V : Set.
// Parameter eq_dec_V : forall (v1 v2:V),{v1=v2}+{~v1=v2}.
// Inductive EA : Set :=
//   nb : Z -> EA | var : V -> EA | pls : EA -> EA -> EA
// | mns : EA -> EA -> EA | mlt : EA -> EA -> EA | dv : EA -> EA -> EA.
constant symbol Vvar : Set
set declared "𝕍var"
definition 𝕍var ≔ τ Vvar

constant symbol EA : Set
set declared "𝔼𝔸"
definition 𝔼𝔸 ≔ τ (EA)
constant symbol ent   : ℕ → 𝔼𝔸                //  /!\ Z !
constant symbol var   : 𝕍var → 𝔼𝔸
constant symbol plus  : 𝔼𝔸 → 𝔼𝔸 → 𝔼𝔸
constant symbol moins : 𝔼𝔸 → 𝔼𝔸 → 𝔼𝔸
constant symbol fois  : 𝔼𝔸 → 𝔼𝔸 → 𝔼𝔸
constant symbol div   : 𝔼𝔸 → 𝔼𝔸 → 𝔼𝔸
symbol EA_ind (p : 𝔼𝔸 → Prop) :
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
constant symbol val : ℕ → 𝕍               //  /!\ Z !
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
//definition Σ {a} ≔ τ a → ℕ
definition Σ ≔ 𝕍var → ℕ

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
symbol eval_EA_fct : Σ → 𝔼𝔸 → 𝕍
rule eval_EA_fct _  (ent $n) ↪ val $n
with eval_EA_fct $s (var $x) ↪ val ($s $x)
with eval_EA_fct $s (plus $a1 $a2)  ↪
     i_plus  (eval_EA_fct $s $a1) (eval_EA_fct $s $a2)
with eval_EA_fct $s (moins $a1 $a2) ↪
     i_moins (eval_EA_fct $s $a1) (eval_EA_fct $s $a2)
with eval_EA_fct $s (fois $a1 $a2)  ↪
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
symbol eval_EA : 𝔼𝔸 → Σ → 𝕍→ Prop
constant symbol eval_var s x :
  π (eval_EA (var x) s (val (s x)))
constant symbol eval_nb  s n :
  π (eval_EA (ent n) s (val n))
constant symbol eval_plus s a1 a2 n1 n2 :
  π (eval_EA a1 s n1) → π (eval_EA a2 s n2) →
  π (eval_EA (plus a1 a2) s (i_plus n1 n2))
// constant symbol eval {a} (s:Σ {a}) a1 a2 n1 n2 :
//  π (eval_EA s (plus a1 a2) (i_plus  (eval_EA s a1) (eval_EA s a2)))
constant symbol eval_moins s a1 a2 n1 n2 :
  π (eval_EA a1 s n1) → π (eval_EA a2 s n2) →
  π (eval_EA (moins a1 a2) s (i_moins n1 n2))
constant symbol eval_fois s a1 a2 n1 n2 :
  π (eval_EA a1 s n1) → π (eval_EA a2 s n2) →
  π (eval_EA (fois a1 a2) s (i_fois n1 n2))
constant symbol eval_div s a1 a2 n1 n2 :
  π (eval_EA a1 s n1) → π (eval_EA a2 s n2) →
  π (eval_EA (div a1 a2) s (i_div n1 n2))

symbol ent_inv s n1 n2 :
  π (eval_EA (ent n1) s (val n2)) → π (n1 = n2)

//compute eval_EA (plus (ent 3) (ent 4)) _ (val (ent 7))
type plus (ent 3) (ent 4)

theorem eval_example s :
π (eval_EA (fois (ent 2) (ent 3)) s (val 6))
proof
  assume s
  apply eval_fois s (ent 2) (ent 3) (val 2) (val 3)
  // 0. π (eval_EA (ent 2) s (val 2))
  apply eval_nb s 2
  // 1. π (eval_EA (ent 3) s (val 3))
  apply eval_nb s 3
qed

theorem det_eval_EA a s v1 v2 :
π (eval_EA a s v1) → π (eval_EA a s v2) → π (v1 = v2)
proof
  assume a s v1 v2
  refine EA_ind (λa, (eval_EA a s v1 ⊃ eval_EA a s v2 ⊃ v1 = v2)) _ _ _ _ _ _ a
  // 0. Πn: τ nat, π (eval_EA (ent n) s v1) → π (eval_EA (ent n) s v2) → π (v1 = v2)
  assume n Hv1 Hv2 fail // apply ent_inv
  // 1. Πx: τ Vvar, π (eval_EA (var x) s v1) → π (eval_EA (var x) s v2) → π (v1 = v2)

  // 2. Πa1: τ EA, (π (eval_EA a1 s v1) → π (eval_EA a1 s v2) → π (v1 = v2)) → Πa2: τ EA, (π (eval_EA a2 s v1) → π (eval_EA a2 s v2) → π (v1 = v2)) → π (eval_EA (plus a1 a2) s v1) → π (eval_EA (plus a1 a2) s v2) → π (v1 = v2)

  // 3. Πa1: τ EA, (π (eval_EA a1 s v1) → π (eval_EA a1 s v2) → π (v1 = v2)) → Πa2: τ EA, (π (eval_EA a2 s v1) → π (eval_EA a2 s v2) → π (v1 = v2)) → π (eval_EA (moins a1 a2) s v1) → π (eval_EA (moins a1 a2) s v2) → π (v1 = v2)

  // 4. Πa1: τ EA, (π (eval_EA a1 s v1) → π (eval_EA a1 s v2) → π (v1 = v2)) → Πa2: τ EA, (π (eval_EA a2 s v1) → π (eval_EA a2 s v2) → π (v1 = v2)) → π (eval_EA (fois a1 a2) s v1) → π (eval_EA (fois a1 a2) s v2) → π (v1 = v2)

  // 5. Πa1: τ EA, (π (eval_EA a1 s v1) → π (eval_EA a1 s v2) → π (v1 = v2)) → Πa2: τ EA, (π (eval_EA a2 s v1) → π (eval_EA a2 s v2) → π (v1 = v2)) → π (eval_EA (div a1 a2) s v1) → π (eval_EA (div a1 a2) s v2) → π (v1 = v2)
qed
