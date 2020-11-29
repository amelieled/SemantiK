require open amelie.lambdapi_examples.Notation
//require open amelie.lambdapi_examples.Nat
// require open amelie.lambdapi_examples.Bool
// require open amelie.lambdapi_examples.Operations
require open amelie.lambdapi_examples.Constructive_logic

constant symbol Z : Set
set declared "ℤ"
definition ℤ ≔ τ Z

symbol plus_int : ℤ → ℤ → ℤ
set infix left 6 "+" ≔ plus_int

symbol mult_int : ℤ → ℤ → ℤ
set infix left 7 "×" ≔ mult_int

symbol minus_int : ℤ → ℤ → ℤ
symbol opp_int   : ℤ → ℤ
// set infix left 6 "-" ≔ minus_int
// set infix 6 "-" ≔ opp_int

// The previous type defines the variable set
// We assume the egality is decidable on Vvar
constant symbol Vvar : Set
set declared "𝕍var"
definition 𝕍var ≔ τ Vvar

constant symbol EA : Set
set declared "𝔼𝔸"
definition 𝔼𝔸 ≔ τ (EA)
constant symbol ent   : ℤ → 𝔼𝔸                //  /!\ Z !
constant symbol var   : 𝕍var → 𝔼𝔸
constant symbol plus  : 𝔼𝔸 → 𝔼𝔸 → 𝔼𝔸
constant symbol fois  : 𝔼𝔸 → 𝔼𝔸 → 𝔼𝔸
constant symbol opp   : 𝔼𝔸 → 𝔼𝔸
symbol EA_ind (p : 𝔼𝔸 → Prop) :
(Πn, π (p (ent n))) →
(Πx, π (p (var x))) →
(Πa1, π (p a1) → Πa2, π (p a2) → π (p (plus a1 a2))) →
(Πa1, π (p a1) → Πa2, π (p a2) → π (p (fois a1 a2))) →
(Πa, π (p a) → π (p (opp a))) →
Πx, π (p x)

// The type of variable valuation
constant symbol S : Set
set declared "Σ"
definition Σ ≔ 𝕍var → ℤ

symbol eval_EA : 𝔼𝔸 → Σ → ℤ→ Prop
constant symbol eval_var s x :
  π (eval_EA (var x) s (s x))
constant symbol eval_nb  s n :
  π (eval_EA (ent n) s n)
constant symbol eval_plus s a1 a2 n1 n2 :
  π (eval_EA a1 s n1) → π (eval_EA a2 s n2) →
  π (eval_EA (plus a1 a2) s (n1 + n2))
constant symbol eval_fois s a1 a2 n1 n2 :
  π (eval_EA a1 s n1) → π (eval_EA a2 s n2) →
  π (eval_EA (fois a1 a2) s (n1 × n2))
constant symbol eval_opp s a n :
  π (eval_EA a s n) →
  π (eval_EA (opp a) s (opp_int n))

symbol ent_inv s n v :
  π (eval_EA (ent n) s v) → π (n = v)
symbol var_inv s x v :
  π (eval_EA (var x) s v) → π (s x = v)
symbol plus_inv s a1 a2 v:
  π (eval_EA (plus a1 a2) s v) →
  π (∃(λn1, ∃(λn2, eval_EA a1 s n1 ∧ eval_EA a2 s n2 ∧ (n1 + n2) = v)))
symbol fois_inv s a1 a2 v:
  π (eval_EA (fois a1 a2) s v) →
  π (∃(λn1, ∃(λn2, eval_EA a1 s n1 ∧ eval_EA a2 s n2 ∧ (n1 × n2) = v)))
symbol opp_inv s a v :
  π (eval_EA (opp a) s v) →
  π (∃(λn, eval_EA a s n ∧ (opp_int n) = v))

symbol arr: Set → Set → Set
set infix right 6 "➭" ≔ arr
rule τ($x ➭ $y) ↪ τ $x → τ $y

theorem exp_deterministe e s v1 v2 : π (eval_EA e s v1 ⊃ eval_EA e s v2 ⊃ v1 = v2)
proof
  refine EA_ind _ _ _ _ _ _
  // Case "ent"
  assume n s v1 v2 Hv1 Hv2
  apply imp_elim (n = v1)
     // 0. π (n = v1) → π (v1 = v2)
     assume Heqvv1 rewrite - Heqvv1 apply ent_inv s refine Hv2
     // 1. π (n = v1)
     apply ent_inv s refine Hv1
  // Case "var"
  assume x s v1 v2 Hv1 Hv2
  apply imp_elim (s x = v1)
     // 0. π (s x = v1) → π (v1 = v2)
     assume Heqxv1 rewrite - Heqxv1 apply var_inv s refine Hv2
     // 1. π (s x = v1)
     apply var_inv s refine Hv1
  // Case "plus"
  assume a1 Ha1 a2 Ha2 s v1 v2 Hv1 Hv2
  apply imp_elim (∃ (λn1, ∃(λn2, eval_EA a1 s n1 ∧ eval_EA a2 s n2 ∧ (n1 + n2) = v1)))
  assume Heq
  apply ex_elim (λn1, ∃ (λn2, eval_EA a1 s n1 ∧ eval_EA a2 s n2 ∧ (n1 + n2) = v1)) _
  apply Heq assume n1 H2
  apply ex_elim (λn2, (eval_EA a1 s n1 ∧ (eval_EA a2 s n2 ∧ ((n1 + n2) = v1))))
  apply H2 assume n2 H3

  apply imp_elim (∃ (λn3, ∃(λn4, eval_EA a1 s n3 ∧ eval_EA a2 s n4 ∧ (n3 + n4) = v2)))
  assume Heq2
  apply ex_elim (λn3, ∃ (λn4, eval_EA a1 s n3 ∧ eval_EA a2 s n4 ∧ (n3 + n4) = v2)) _
  apply Heq2 assume n3 H22
  apply ex_elim (λn4, (eval_EA a1 s n3 ∧ (eval_EA a2 s n4 ∧ ((n3 + n4) = v2))))
  apply H22 assume n4 H32

  apply imp_elim ((n1 + n2) = v1) assume Hplus rewrite - Hplus
  apply imp_elim ((n3 + n4) = v2) assume Hplus2 rewrite - Hplus2
  apply imp_elim (n1 = n3) assume Hn1n3 rewrite Hn1n3
  apply imp_elim (n2 = n4) assume Hn2n4 rewrite Hn2n4 reflexivity
  apply Ha2 s n2 n4
  apply conj_elim_left _ ((n1 + n2) = v1)
  apply conj_elim_right (eval_EA a1 s n1) apply H3

  apply conj_elim_left _ ((n3 + n4) = v2)
  apply conj_elim_right (eval_EA a1 s n3) apply H32

  apply Ha1 s n1 n3
  apply conj_elim_left _ (eval_EA a2 s n2 ∧ ((n1 + n2) = v1)) apply H3

  apply conj_elim_left _ (eval_EA a2 s n4 ∧ ((n3 + n4) = v2)) apply H32

  apply conj_elim_right (eval_EA a2 s n4)
  apply conj_elim_right (eval_EA a1 s n3) apply H32

  apply conj_elim_right (eval_EA a2 s n2)
  apply conj_elim_right (eval_EA a1 s n1) apply H3

  apply plus_inv s a1 a2 apply Hv2
  apply plus_inv s a1 a2 apply Hv1

   // Case "fois"

  assume a1 Ha1 a2 Ha2 s v1 v2 Hv1 Hv2
  apply imp_elim (∃ (λn1, ∃(λn2, eval_EA a1 s n1 ∧ eval_EA a2 s n2 ∧ (n1 × n2) = v1)))
  assume Heq
  apply ex_elim (λn1, ∃ (λn2, eval_EA a1 s n1 ∧ eval_EA a2 s n2 ∧ (n1 × n2) = v1)) _
  apply Heq assume n1 H2
  apply ex_elim (λn2, (eval_EA a1 s n1 ∧ (eval_EA a2 s n2 ∧ ((n1 × n2) = v1))))
  apply H2 assume n2 H3

  apply imp_elim (∃ (λn3, ∃(λn4, eval_EA a1 s n3 ∧ eval_EA a2 s n4 ∧ (n3 × n4) = v2)))
  assume Heq2
  apply ex_elim (λn3, ∃ (λn4, eval_EA a1 s n3 ∧ eval_EA a2 s n4 ∧ (n3 × n4) = v2)) _
  apply Heq2 assume n3 H22
  apply ex_elim (λn4, (eval_EA a1 s n3 ∧ (eval_EA a2 s n4 ∧ ((n3 × n4) = v2))))
  apply H22 assume n4 H32

  apply imp_elim ((n1 × n2) = v1) assume Hplus rewrite - Hplus
  apply imp_elim ((n3 × n4) = v2) assume Hplus2 rewrite - Hplus2
  apply imp_elim (n1 = n3) assume Hn1n3 rewrite Hn1n3
  apply imp_elim (n2 = n4) assume Hn2n4 rewrite Hn2n4 reflexivity
  apply Ha2 s n2 n4
  apply conj_elim_left _ ((n1 × n2) = v1)
  apply conj_elim_right (eval_EA a1 s n1) apply H3

  apply conj_elim_left _ ((n3 × n4) = v2)
  apply conj_elim_right (eval_EA a1 s n3) apply H32

  apply Ha1 s n1 n3
  apply conj_elim_left _ (eval_EA a2 s n2 ∧ ((n1 × n2) = v1)) apply H3

  apply conj_elim_left _ (eval_EA a2 s n4 ∧ ((n3 × n4) = v2)) apply H32

  apply conj_elim_right (eval_EA a2 s n4)
  apply conj_elim_right (eval_EA a1 s n3) apply H32

  apply conj_elim_right (eval_EA a2 s n2)
  apply conj_elim_right (eval_EA a1 s n1) apply H3

  apply fois_inv s a1 a2 apply Hv2
  apply fois_inv s a1 a2 apply Hv1

  // Case "opp"
  assume a Ha s v1 v2 Hv1 Hv2
  apply imp_elim (∃ (λn, eval_EA a s n ∧ (opp_int n) = v1))
  assume Heq
  apply ex_elim (λn, eval_EA a s n ∧ (opp_int n) = v1) _
  apply Heq assume n1 H2

  apply imp_elim (∃ (λn, eval_EA a s n ∧ (opp_int n) = v2))
  assume Heq2
  apply ex_elim (λn, eval_EA a s n ∧ (opp_int n) = v2) _
  apply Heq2 assume n2 H22

  apply imp_elim ((opp_int n1) = v1) assume Hplus rewrite - Hplus
  apply imp_elim ((opp_int n2) = v2) assume Hplus2 rewrite - Hplus2
  apply imp_elim (n1 = n2) assume Hn1n2 rewrite Hn1n2 reflexivity
  apply Ha s n1 n2
  apply conj_elim_left _ ((opp_int n1) = v1) apply H2
  apply conj_elim_left _ ((opp_int n2) = v2) apply H22
  apply conj_elim_right (eval_EA a s n2) apply H22
  apply conj_elim_right (eval_EA a s n1) apply H2

  apply opp_inv s a apply Hv2
  apply opp_inv s a apply Hv1

qed
