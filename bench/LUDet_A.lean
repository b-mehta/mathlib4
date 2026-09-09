/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.LU
public import Mathlib.Tactic.NormNum.Result

public meta import Mathlib.Tactic.NormNum

/-!
# The `lu_det` tactic

The `lu_det` tactic proves determinant equalities for explicit matrices over fields of
characteristic zero when the matrix entries and determinant are rational numerals.
-/

public section

namespace Mathlib.Tactic.LUDet

/-- An `IsRat` certificate identifies `e` with the cast of `mkRat n d`. -/
theorem eq_ratCast_of_isRat {K : Type*} [DivisionRing K] [CharZero K] {e : K} {n : ℤ}
    {d : ℕ} (h : Mathlib.Meta.NormNum.IsRat e n d) : e = (mkRat n d : K) := by
  obtain ⟨inv, rfl⟩ := h
  rw [Rat.mkRat_eq_div, Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast,
    div_eq_mul_inv, invOf_eq_inv]

end Mathlib.Tactic.LUDet

end

meta section

open Lean Elab Meta Qq

namespace Mathlib.Tactic.LUDet

/-- Computes an LU decomposition of `A`. The returned matrix stores the strict lower triangle
of a unit lower-triangular `L` and the upper-triangular `U`; the pairs record row swaps. -/
def luDecompose {n : ℕ} (A : Vector (Vector ℚ n) n) :
    Vector (Vector ℚ n) n × List (ℕ × ℕ) := Id.run do
  let mut LU := A
  let mut swaps : Array (ℕ × ℕ) := #[]
  for h : k in [0:n] do
    have hk : k < n := h.upper
    if LU[k][k] = 0 then
      if let some p := (List.finRange n).find? fun p ↦ decide (k < p.val ∧ LU[p][k] ≠ 0) then
        swaps := swaps.push (k, p.val)
        LU := LU.swap k p.val
    let pivotRow := LU[k]
    let pivot := pivotRow[k]
    unless pivot = 0 do
      for h' : i in [k+1:n] do
        have hi : i < n := h'.upper
        let f := LU[i][k] / pivot
        let mut row := LU[i].set k f
        for h'' : j in [k+1:n] do
          have hj : j < n := h''.upper
          row := row.set j (row[j] - f * pivotRow[j])
        LU := LU.set i row
  return (LU, swaps.toList)

/-- A matrix entry and its rational evaluation. -/
structure Entry {u : Level} (K : Q(Type u)) where
  x : Q($K)
  val : ℚ
  valE : Q(ℚ)
  pf : Expr

/-- Builds rational entries and proves that casting them gives the reflected row. -/
def rowOfFnProof {u : Level} {K : Q(Type u)} (fieldInst : Q(Field $K))
    (entries : List (Entry K)) (finalTail : Expr) :
    Q(List ℚ) × Expr :=
  have tail0 : Q(Fin 0 → $K) := finalTail
  let base : Q(List ℚ) × Expr × Expr × ℕ := (q([]), q(List.ofFn_zero (f := $tail0)), tail0, 0)
  let (lst, prf, _, _) := entries.foldr (init := base)
    fun e acc ↦
      let (lst, proof, tail, m) := acc
      have x : Q($K) := e.x
      have y : Q(ℚ) := e.valE
      have hy : Q($x = ($y : $K)) := e.pf
      have mE : Q(ℕ) := mkRawNatLit m
      have tail : Q(Fin $mE → $K) := tail
      have prf : Q(List.ofFn $tail = ($lst).map Rat.cast) := proof
      (q($y :: $lst), q(LUDet.list_ofFn_vecCons id $x $tail $hy $prf),
        q(Matrix.vecCons $x $tail), m + 1)
  (lst, prf)

/-- Builds rational rows and proves that casting their entries gives the reflected matrix. -/
def rowsOfFnProof {u : Level} {K : Q(Type u)} (fieldInst : Q(Field $K)) (n : Q(ℕ))
    (outerRows : Array Q(Fin $n → $K)) (outerLast : Expr)
    (rowData : Array (List (Entry K) × Expr)) :
    Q(List (List ℚ)) × Expr :=
  have last0 : Q(Fin 0 → Fin $n → $K) := outerLast
  let base : Q(List (List ℚ)) × Expr × Expr × ℕ :=
    (q([]), q(List.ofFn_zero (f := fun i ↦ List.ofFn ($last0 i))), outerLast, 0)
  let (lst, proof, _, _) := (outerRows.zip rowData).foldr (init := base)
    fun (rvec, entries, last) acc ↦
      let (lst, proof, tail, m) := acc
      let (xs, rowProof) := rowOfFnProof fieldInst entries last
      have mE : Q(ℕ) := mkRawNatLit m
      have rtail : Q(Fin $mE → Fin $n → $K) := tail
      have rprf : Q(List.ofFn $rvec = List.map Rat.cast $xs) := rowProof
      have prf : Q(List.ofFn (fun i ↦ List.ofFn ($rtail i)) =
          List.map (List.map Rat.cast) $lst) := proof
      (q($xs :: $lst), q(LUDet.list_ofFn_vecCons List.ofFn $rvec $rtail $rprf $prf),
        q(Matrix.vecCons $rvec $rtail), m + 1)
  (lst, proof)

/-- Evaluates `e` as a rational numeral, using `what` to identify an invalid expression. -/
def evalEntry {u : Level} (K : Q(Type u)) (fieldInst : Q(Field $K))
    (_charZeroInst : Q(CharZero $K)) (e : Q($K)) (what : MessageData) :
    MetaM (Entry K) := do
  let r ← try Mathlib.Meta.NormNum.derive (u := u) (α := K) e
    catch _ => throwError "lu_det: {what} is not a rational numeral: {e}"
  let some ⟨v, num, den, prf⟩ := r.toRat' q(inferInstance)
    | throwError "lu_det: {what} is not a rational numeral: {e}"
  return ⟨e, v, q(mkRat $num $den), q(LUDet.eq_ratCast_of_isRat $prf)⟩

/-- Converts `a` to a vector of length `n`, reporting an invalid matrix literal on mismatch. -/
def toVectorOfLen {α : Type} (n : ℕ) (a : Array α) : MetaM (Vector α n) := do
  if h : a.size = n then return a.toVector.cast h
  else throwError "lu_det: matrix is not a `!![...]` literal"

/-- Closes `Matrix.det !![...] = d` when the field has characteristic zero and all displayed
values are rational numerals. -/
def luDetTactic (g : MVarId) : MetaM Unit := do
  let tgt : Q(Prop) ← instantiateMVars (← g.getType)
  let ~q($lhs = $d) := tgt
    | throwError "lu_det: goal is not of the form `Matrix.det M = d`"
  let_expr Matrix.det ixType _ _ K _ M := lhs
    | throwError "lu_det: goal is not of the form `Matrix.det M = d`"
  let_expr Fin nE := (← whnfR ixType)
    | throwError "lu_det: the matrix is not indexed by `Fin n`"
  have nE : Q(ℕ) := nE
  let some n ← getNatValue? nE
    | throwError "lu_det: matrix dimension is not a numeral"
  let u ← getDecLevel K
  have K : Q(Type u) := K
  let fieldInst : Q(Field $K) ← synthInstanceQ q(Field $K)
  let charZeroInst : Q(CharZero $K) ← synthInstanceQ q(CharZero $K)
  have M : Q(Matrix (Fin $nE) (Fin $nE) $K) := M
  have d : Q($K) := d
  let ~q(Matrix.of $rowsVec) := M
    | throwError "lu_det: matrix is not a `!![...]` literal"
  let (outerRows, _, outerLast) ← Matrix.matchVecConsPrefix nE rowsVec
  let outerRows := outerRows.toArray
  let rowPeels ← outerRows.mapM fun row ↦ Matrix.matchVecConsPrefix nE row
  let entryRows : Array (Array (Entry K)) ← rowPeels.mapIdxM fun i (entries, _, _) ↦
    entries.toArray.mapIdxM fun j x ↦
      evalEntry K fieldInst charZeroInst x m!"matrix entry ({i}, {j})"
  let entryRows : Vector (Vector (Entry K) n) n ←
    toVectorOfLen n (← entryRows.mapM (toVectorOfLen n))
  let vals := entryRows.map (·.map (·.val))
  let rhs ← evalEntry K fieldInst charZeroInst d m!"the right-hand side"
  have dq : Q(ℚ) := rhs.valE
  let (luVals, swaps) := luDecompose vals
  let sign : ℚ := if swaps.length % 2 = 0 then 1 else -1
  let detVal : ℚ := (List.finRange n).foldl (fun acc i ↦ acc * luVals[i][i]) sign
  unless detVal = rhs.val do
    throwError "lu_det: the determinant is {detVal}, but the goal claims {rhs.val}"
  have lRows : Q(List (List ℚ)) := toExpr <| List.ofFn fun i : Fin n ↦
    List.ofFn fun j : Fin (i.val + 1) ↦ if i.val = j.val then 1 else luVals[i][j.val]
  have vRows : Q(List (List ℚ)) := toExpr <| List.ofFn fun i : Fin n ↦
    List.ofFn fun j : Fin (i.val + 1) ↦ luVals[j.val][i.val]
  have swapsE : Q(List (ℕ × ℕ)) := toExpr swaps
  let rowData := (entryRows.toArray.zip rowPeels).map fun (row, _, _, last) ↦ (row.toList, last)
  let (aRows, hAExpr) := rowsOfFnProof fieldInst nE outerRows outerLast rowData
  have hA : Q((List.ofFn fun i ↦ List.ofFn fun j ↦ $M i j) =
      List.map (List.map (↑)) $aRows) := hAExpr
  have hdK : Q($d = ($dq : $K)) := rhs.pf
  have hcert : Q(LUDet.checkCertificate $nE $aRows $lRows $vRows $swapsE $dq) := reflBoolTrue
  g.assign q(LUDet.det_eq_of_lu $M $aRows $lRows $vRows $swapsE $dq $d $hA $hcert $hdK)

/--
`lu_det` proves goals of the form `Matrix.det !![...] = d`, where the matrix lives in a
field of characteristic zero and every matrix entry and `d` is a rational numeral.

```lean
example : Matrix.det (R := ℝ) !![1, 2; 3, 4] = -2 := by lu_det
```
-/
elab "lu_det" : tactic => Tactic.liftMetaFinishingTactic luDetTactic

end Mathlib.Tactic.LUDet

end
