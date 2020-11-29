// Imp: Simple Imperative Programs

// This file is the translation of the file Imp.v (Tome 1 - Software Foundations)
require open amelie.lambdapi_examples.Notation
require open amelie.lambdapi_examples.Bool

set builtin "Prop"     ≔ Prop

constant symbol nat : Set // Natural number
inductive Nat : TYPE ≔
 | z    : Nat
 | succ : Nat → Nat
rule Nat ↪ τ nat

set builtin "0"  ≔ z
set builtin "+1" ≔ succ
///////////////////////////////////////////
// Arithmetic and Boolean Expressions
///////////////////////////////////////////

inductive aexp : TYPE ≔
 | ANum   : Πn:Nat, aexp
 | APlus  : Πa1:aexp, Πa2 : aexp, aexp
 | AMinus : Πa1:aexp, Πa2 : aexp, aexp
 | AMult  : Πa1:aexp, Πa2 : aexp, aexp

inductive bexp : TYPE ≔
 | BTrue  : bexp
 | BFalse : bexp
 | BEq    : Πa1:aexp, Πa2 : aexp, bexp
 | BLe    : Πa1:aexp, Πa2 : aexp, bexp
 | BNot   : Πb:bexp, bexp
 | BAnd   : Πb1:bexp, Πb2 : bexp, bexp

///////////////////////////////////////////
// Evaluation
///////////////////////////////////////////

symbol plus : Nat → Nat → Nat
set infix left 6 "+" ≔ plus
rule       z + $y ↪ $y
with succ $x + $y ↪ succ ($x + $y)

symbol mult : Nat → Nat → Nat
set infix left 7 "×" ≔ mult
rule       z × _  ↪ z
with succ $x × $y ↪ $y + $x × $y

symbol sub : Nat → Nat → Nat
set infix left 7 "-" ≔ sub
rule     z  - z        ↪ z
with succ _ - z        ↪ z
with     z - succ _    ↪ z
with succ $x - succ $y ↪ $x - $y

symbol aeval : aexp → Nat
rule aeval (ANum $n) ↪ $n
with aeval (APlus  $a1 $a2) ↪ (aeval $a1) + (aeval $a2)
with aeval (AMinus $a1 $a2) ↪ (aeval $a1) - (aeval $a2)
with aeval (AMult  $a1 $a2) ↪ (aeval $a1) × (aeval $a2)

theorem ex_test_aeval1 : π (aeval (APlus (ANum 2) (ANum 2)) = 4)
proof
 reflexivity
qed


//symbol eqb : 𝔹→ 𝔹→ 𝔹
// rule eqb true  $b ↪ $b
// with eqb false $b ↪ not $b

symbol eqb : Nat → Nat → 𝔹
rule eqb    z         z      ↪ true
with eqb (succ $x) (succ $y) ↪ eqb $x $y
with eqb    z      (succ  _) ↪ false
with eqb (succ  _)    z      ↪ false

symbol leb : Nat → Nat → 𝔹
rule leb     z         z         ↪ true
with leb    z      (succ _)      ↪ true
with leb (succ $m) (succ $n) ↪ leb $m $n
with leb (succ _)      z     ↪ false

symbol beval : bexp → 𝔹
rule beval BTrue          ↪ true
with beval BFalse         ↪ false
with beval (BEq $a1 $a2)  ↪ eqb (aeval $a1) (aeval $a2)
with beval (BLe $a1 $a2)  ↪ leb (aeval $a1) (aeval $a2)
with beval (BNot $b)      ↪ neg (beval $b)
with beval (BAnd $b1 $b2) ↪ andb (beval $b1) (beval $b2)

///////////////////////////////////////////
// Optimization
///////////////////////////////////////////

symbol opti_0plus : aexp → aexp
rule opti_0plus (ANum $n) ↪ (ANum $n)
with opti_0plus (APlus (ANum z) $e) ↪ opti_0plus $e
with opti_0plus (APlus  $e1 $e2)    ↪ APlus  (opti_0plus $e1) (opti_0plus $e2)
with opti_0plus (AMinus $e1 $e2)    ↪ AMinus (opti_0plus $e1) (opti_0plus $e2)
with opti_0plus (AMult  $e1 $e2)    ↪ AMult  (opti_0plus $e1) (opti_0plus $e2)

// theorem test_opti_0plus :
//   π (opti_0plus (APlus (ANum 2)
//                        (APlus (ANum 0)
//                               (APlus (ANum 0) (ANum 1))))
//                 = APlus (ANum 2) (ANum 1))
// proof
// qed

theorem optimize_0plus_sound: Π a, π (aeval (opti_0plus a) = aeval a)
proof
  assume a
  refine ind_aexp (λp, aeval (opti_0plus p) = aeval p) _ _ _ _ a
  // 0. Πx: τ nat, π (aeval (opti_0plus (ANum x)) = aeval (ANum x))
  assume x reflexivity
  // 1. Πx: aexp, π (aeval (opti_0plus x) = aeval x) →
  //    Πx0: aexp, π (aeval (opti_0plus x0) = aeval x0) →
  //      π (aeval (opti_0plus (APlus x x0)) = aeval (APlus x x0))
  assume x Hx x0 Hx0
  refine ind_aexp (λp, aeval (opti_0plus (APlus p x0)) = aeval (APlus p x0)) _ _ _ _ x
     simpl assume x1
     refine ind_Nat (λp, (p + aeval (opti_0plus x0)) = (p + aeval x0)) _ _ x1
         apply Hx0
         assume x2 Hx2 simpl rewrite Hx2 reflexivity
     simpl assume x1 Hx1 x2 Hx2 rewrite Hx0
 simpl
  // 2. Πx: aexp, π (aeval (opti_0plus x) = aeval x) →
  //    Πx0: aexp, π (aeval (opti_0plus x0) = aeval x0) →
  //        π (aeval (opti_0plus (AMinus x x0)) = aeval (AMinus x x0))

  // 3. Πx: aexp, π (aeval (opti_0plus x) = aeval x) →
  //    Πx0: aexp, π (aeval (opti_0plus x0) = aeval x0) →
  //        π (aeval (opti_0plus (AMult x x0)) = aeval (AMult x x0))
qed
