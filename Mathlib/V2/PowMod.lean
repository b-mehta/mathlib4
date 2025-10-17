/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.NormNum.PowMod

/-!
# Proof-producing evaluation of `a ^ b % n`

Note that `Mathlib.Tactic.NormNum.PowMod` contains a similar tactic, but that runs significantly
slower and less efficiently than the one here.
-/

open Nat

/-- The pow-mod function, named explicitly to allow more precise control of reduction. -/
def powMod (a b n : ℕ) : ℕ := a ^ b % n
/-- The pow-mod auxiliary function, named explicitly to allow more precise control of reduction. -/
def powModAux (a b c n : ℕ) : ℕ := (a ^ b * c) % n

lemma powModAux_zero_eq {a c n m : ℕ} (hm : c % n = m) : powModAux a 0 c n = m := by
  simpa [powModAux]

lemma powModAux_one_eq {a c n m : ℕ} (hm : (a * c) % n = m) : powModAux a 1 c n = m := by
  simp_all [powModAux]

lemma powModAux_even_eq {a a' b b' c n m : ℕ}
    (ha' : a * a % n = a') (hb' : b' <<< 1 = b)
    (h : powModAux a' b' c n = m) :
    powModAux a b c n = m := by
  rw [← ha', powModAux, mul_mod] at h
  rw [Nat.shiftLeft_eq, mul_comm, pow_one] at hb'
  rw [← hb', powModAux, pow_mul, mul_mod, pow_two, pow_mod, h]

lemma powModAux_odd_eq {a a' b b' c c' n m : ℕ}
    (hb' : 2 * b' + 1 = b) (ha' : a * a % n = a') (hc' : a * c % n = c')
    (h : powModAux a' b' c' n = m) :
    powModAux a b c n = m := by
  rw [← ha', ← hc', powModAux, mul_mod, mod_mod] at h
  rw [← hb', powModAux, pow_succ, pow_mul, mul_assoc, mul_mod, pow_mod, pow_two, h]

lemma powMod_eq (a : ℕ) {a' b n m : ℕ} (h : powModAux a' b 1 n = m) (ha : a % n = a') :
    powMod a b n = m := by
  rwa [powModAux, mul_one, ← ha, pow_mod, mod_mod, ← pow_mod] at h

lemma powMod_ne {a b n m : ℕ} (m' : ℕ) (hm : bne m' m) (h : powMod a b n = m') :
    powMod a b n ≠ m := by
  simp_all

noncomputable def powModTR (a b n : Nat) : Nat :=
  aux b.succ (a.mod n) b 1
where
  aux : Nat → ((a b c : Nat) → Nat) :=
    Nat.rec (fun _ _ _ => 0)
      (fun _ r a b c =>
        (b.beq 0).rec
          ((b.beq 1).rec
            (((b.mod 2).beq 0).rec
                (r ((a.mul a).mod n) (b.div 2) ((a.mul c).mod n))
                (r ((a.mul a).mod n) (b.div 2) c))
            ((a.mul c).mod n))
          (c.mod n))

def powModTR' (a b n : ℕ) : ℕ :=
  aux (a % n) b 1
  where aux (a b c : ℕ) : ℕ :=
    if b = 0 then c % n
    else if b = 1 then (a * c) % n
    else if b % 2 = 0 then
      aux (a * a % n) (b / 2) c
    else
      aux (a * a % n) (b / 2) (a * c % n)
    partial_fixpoint

lemma Bool.rec_eq_ite {α : Type*} {b : Bool} {t f : α} : b.rec f t = if b then t else f := by
  cases b <;> simp

@[simp] lemma Nat.mod_eq_mod {a b : ℕ} : a.mod b = a % b := rfl
@[simp] lemma Nat.div_eq_div {a b : ℕ} : a.div b = a / b := rfl
@[simp] lemma Nat.land_eq_land {a b : ℕ} : a.land b = a &&& b := rfl

@[simp] lemma powModTR_aux_zero_eq {n a b c : ℕ} :
    powModTR.aux n 0 a b c = 0 := rfl

lemma powModTR_aux_succ_eq {n a b c fuel : ℕ} :
    powModTR.aux n (fuel + 1) a b c =
      (b.beq 0).rec (true := c % n)
      ((b.beq 1).rec (true := (a * c) % n)
      (((b % 2).beq 0).rec
          (powModTR.aux n fuel (a * a % n) (b / 2) (a * c % n))
          (powModTR.aux n fuel (a * a % n) (b / 2) c))) := by
  rfl

lemma powModTR_aux_succ_eq' {n a b c fuel : ℕ} :
    powModTR.aux n (fuel + 1) a b c =
      if b = 0 then c % n else
      if b = 1 then a * c % n else
      if b % 2 = 0 then powModTR.aux n fuel (a * a % n) (b / 2) c
      else powModTR.aux n fuel (a * a % n) (b / 2) (a * c % n) := by
  simp only [powModTR_aux_succ_eq, Bool.rec_eq_ite, beq_eq]

lemma powModTR_aux_eq (n a b c fuel) (hfuel : b < fuel) :
    powModTR.aux n fuel a b c = powModAux a b c n := by
  induction fuel generalizing a b c with
  | zero => omega
  | succ fuel ih =>
    rw [powModTR_aux_succ_eq']
    split
    case isTrue hb0 => rw [hb0, powModAux, pow_zero, one_mul]
    split
    case isTrue hb1 => rw [hb1, powModAux, pow_one]
    split
    case isTrue hb0 hbe =>
      rw [ih _ _ _ (by omega)]
      rw [powModAux, powModAux, Nat.mul_mod _ c, Nat.mul_mod _ c]
      conv_rhs =>
        rw [← Nat.mod_add_div b 2]
      rw [hbe, zero_add, pow_mul, ← pow_two, ← Nat.pow_mod]
    case isFalse hb0 hbo =>
      rw [ih _ _ _ (by omega)]
      rw [powModAux, powModAux, Nat.mul_mod, Nat.mod_mod, ← pow_two,
        ← Nat.pow_mod, ← Nat.pow_mul, ← Nat.mul_mod, ← mul_assoc, ← Nat.pow_add_one]
      congr! 3
      cutsat

lemma powModTR_eq (a b n : ℕ) : powModTR a b n = powMod a b n := by
  rw [powModTR, powModTR_aux_eq _ _ _ _ _ (by omega)]
  rw [powModAux, mul_one, powMod, mod_eq_mod, ← Nat.pow_mod]

lemma powMod_eq_of_powModTR (a b n m : ℕ) (h : (powModTR a b n).beq m) : powMod a b n = m := by
  rwa [powModTR_eq, beq_eq] at h

lemma powMod_ne_of_powModTR (a b n m : ℕ) (h : (powModTR a b n).beq m = false) :
    powMod a b n ≠ m := by
  have := Nat.ne_of_beq_eq_false h
  rwa [powModTR_eq] at this

namespace Tactic.powMod

open Lean Meta Elab Tactic

/-- Given `a, b, c, n : ℕ`, return `(m, ⊢ ℕ, ⊢ powModAux a b c n = m)`. -/
def mkPowModAuxEq (a b c n : ℕ) (aE bE cE nE : Expr) : MetaM (ℕ × Expr × Expr) :=
  if b = 0 then do
    let m : ℕ := c % n
    let mE : Expr := mkNatLit m
    let hm : Expr ← mkEqRefl mE
    return (m, mE, mkApp5 (mkConst ``powModAux_zero_eq []) aE cE nE mE hm)
  else if b = 1 then do
    let m : ℕ := (a * c) % n
    let mE : Expr := mkNatLit m
    let hm : Expr ← mkEqRefl mE
    return (m, mE, mkApp5 (mkConst ``powModAux_one_eq []) aE cE nE mE hm)
  else if Even b then do
    let b' := b / 2
    let a' := a * a % n
    let a'E := mkNatLit a'
    let b'E := mkNatLit b'
    let ha' : Expr ← mkEqRefl a'E
    let hb' : Expr ← mkEqRefl bE
    let (m, mE, eq) ← mkPowModAuxEq a' b' c n a'E b'E cE nE
    return (m, mE, mkApp10 (mkConst ``powModAux_even_eq []) aE a'E bE b'E cE nE mE ha' hb' eq)
  else do
    let a' := a * a % n
    let b' := b / 2
    let c' := a * c % n
    let a'E := mkNatLit a'
    let b'E := mkNatLit b'
    let c'E := mkNatLit c'
    let hb' : Expr ← mkEqRefl bE
    let ha' : Expr ← mkEqRefl a'E
    let hc' : Expr ← mkEqRefl c'E
    let (m, mE, eq) ← mkPowModAuxEq a' b' c' n a'E b'E c'E nE
    return (m, mE,
      mkApp5 (mkApp7 (mkConst ``powModAux_odd_eq []) aE a'E bE b'E cE c'E nE) mE hb' ha' hc' eq)

/-- Given `a, b, n : ℕ`, return `(m, ⊢ powMod a b n = m)`. -/
def mkPowModEq (a b n : ℕ) (aE bE nE : Expr) : MetaM (ℕ × Expr × Expr) := do
  let a' := a % n
  let a'E := mkNatLit a'
  let (m, mE, eq) ← mkPowModAuxEq a' b 1 n a'E bE (mkNatLit 1) nE
  return (m, mE, ← mkAppM ``powMod_eq #[aE, eq, ← mkEqRefl a'E])

/-- Given `a, b, n, m : ℕ`, if `powMod a b n = m` then return a proof of that fact. -/
def provePowModEq (a b n m : ℕ) (aE bE nE : Expr) : MetaM Expr := do
  let (m', _, eq) ← mkPowModEq a b n aE bE nE
  unless m = m' do throwError "attempted to prove {a} ^ {b} % {n} = {m} but it's actually {m'}"
  return eq

/-- Given `a, b, n, m : ℕ`, if `powMod a b n ≠ m` then return a proof of that fact. -/
def provePowModNe (a b n m : ℕ) (aE bE nE mE : Expr) : MetaM Expr := do
  let (m', m'E, eq) ← mkPowModEq a b n aE bE nE
  if m = m' then throwError "attempted to prove {a} ^ {b} % {n} ≠ {m} but it is {m'}"
  let ne := eagerReflBoolTrue
  return mkApp7 (mkConst ``powMod_ne []) aE bE nE mE m'E ne eq

/-- Given `a, b, n : ℕ`, return `(m, ⊢ powMod a b n = m)`. -/
def mkPowModEq' (a b n : ℕ) (aE bE nE : Expr) : MetaM (ℕ × Expr × Expr) := do
  let m := powModTR' a b n
  let mE := mkNatLit m
  return (m, mE, mkApp5 (mkConst ``powMod_eq_of_powModTR) aE bE nE mE eagerReflBoolTrue)

/-- Given `a, b, n, m : ℕ`, if `powMod a b n = m` then return a proof of that fact. -/
def provePowModEq' (a b n m : ℕ) (aE bE nE : Expr) : MetaM Expr := do
  let (m', _, eq) ← mkPowModEq' a b n aE bE nE
  unless m = m' do throwError "attempted to prove {a} ^ {b} % {n} = {m} but it's actually {m'}"
  return eq

/-- Given `a, b, n, m : ℕ`, if `powMod a b n ≠ m` then return a proof of that fact. -/
def provePowModNe' (a b n m : ℕ) (aE bE nE mE : Expr) : MetaM Expr := do
  let m' := powModTR' a b n
  if m = m' then throwError "attempted to prove {a} ^ {b} % {n} ≠ {m} but it is {m'}"
  return mkApp5 (mkConst ``powMod_ne_of_powModTR) aE bE nE mE eagerReflBoolFalse

def prove_pow_mod_tac_aux (eq ne : ℕ → ℕ → ℕ → ℕ → Expr → Expr → Expr → Expr → MetaM Expr)
    (g : MVarId) : MetaM Unit := do
  let t : Expr ← g.getType
  match_expr t with
  | Eq ty lhsE rhsE =>
    unless (← whnfR ty).isConstOf ``Nat do throwError "not an equality of naturals"
    let some rhs := rhsE.nat? | throwError "rhs is not a numeral"
    let some (aE, bE, nE) := lhsE.app3? ``powMod | throwError "lhs is not a pow-mod"
    let some a := aE.nat? | throwError "base is not a numeral"
    let some b := bE.nat? | throwError "exponent is not a numeral"
    let some n := nE.nat? | throwError "modulus is not a numeral"
    let pf ← eq a b n rhs aE bE nE rhsE
    g.assign pf
  | Ne ty lhsE rhsE =>
    unless (← whnfR ty).isConstOf ``Nat do throwError "not an equality of naturals"
    let some rhs := rhsE.nat? | throwError "rhs is not a numeral"
    let some (aE, bE, nE) := lhsE.app3? ``powMod | throwError "lhs is not a pow-mod"
    let some a := aE.nat? | throwError "base is not a numeral"
    let some b := bE.nat? | throwError "exponent is not a numeral"
    let some n := nE.nat? | throwError "modulus is not a numeral"
    let pf ← ne a b n rhs aE bE nE rhsE
    g.assign pf
  | _ => throwError "not an accepted expression"

def prove_pow_mod_tac (g : MVarId) : MetaM Unit :=
  prove_pow_mod_tac_aux
    (fun a b n m aE bE nE _ ↦ provePowModEq a b n m aE bE nE)
    provePowModNe g

def prove_pow_mod_tac2 (g : MVarId) : MetaM Unit :=
  prove_pow_mod_tac_aux
    (fun a b n m aE bE nE _ ↦ provePowModEq' a b n m aE bE nE)
    provePowModNe' g

elab "prove_pow_mod" : tactic => liftMetaFinishingTactic prove_pow_mod_tac
elab "prove_pow_mod2" : tactic => liftMetaFinishingTactic prove_pow_mod_tac2

end Tactic.powMod

example :
    powMod 2
      2112421871326486211461011031931945323874719289347729538762174157135451276986
      2112421871326486211461011031931945323874719289347729538762174157135451276987 =
      1 := by
  prove_pow_mod

example :
    powMod 2
      2112421871326486211461011031931945323874719289347729538762174157135451276986
      2112421871326486211461011031931945323874719289347729538762174157135451276987 =
      1 := by
  prove_pow_mod2

example : powMod 2304821 1 2308 = 1437 := by
  prove_pow_mod

example : powMod 2 23408 2307 = 778 := by
  prove_pow_mod

example : powMod 2 23408 2307 ≠ 1 := by
  prove_pow_mod

example : powMod 2 385273928 1000000007 = 3 := by
  prove_pow_mod
