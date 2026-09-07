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
  lit : Q(ℚ)
  cast : Q($K)
  pf : Q($x = $cast)

/-- Builds rational entries and proves that casting them gives the reflected row. -/
def rowOfFnProof {u : Level} {K : Q(Type u)} (fieldInst : Q(Field $K))
    (entries : List (Entry K)) (finalTail : Expr) :
    Q(List ℚ) × Expr :=
  have tail0 : Q(Fin 0 → $K) := finalTail
  let base : Q(List ℚ) × Expr × Expr × ℕ :=
    (q([]), q(List.ofFn_zero (f := $tail0)), tail0, 0)
  let (lst, prf, _, _) := entries.foldr
    (fun e acc ↦
      let (lst, prfE, tailE, m) := acc
      have x : Q($K) := e.x
      have y : Q(ℚ) := e.lit
      have yK : Q($K) := e.cast
      have hy : Q($x = $yK) := e.pf
      have m' : Q(ℕ) := mkRawNatLit m
      have tail : Q(Fin $m' → $K) := tailE
      have prf : Q(List.ofFn $tail = List.map Rat.cast $lst) := prfE
      (q($y :: $lst), q(LUDet.list_ofFn_vecCons id $x $tail $hy $prf),
        q(Matrix.vecCons $x $tail), m + 1))
    base
  (lst, prf)

/-- Builds rational rows and proves that casting their entries gives the reflected matrix. -/
def rowsOfFnProof {u : Level} {K : Q(Type u)} (fieldInst : Q(Field $K)) (n : Q(ℕ))
    (outerRows : Array Q(Fin $n → $K)) (outerLast : Expr)
    (rowData : Array (List (Entry K) × Expr)) :
    Q(List (List ℚ)) × Expr := Id.run do
  let mut lst : Q(List (List ℚ)) := q([])
  have last0 : Q(Fin 0 → Fin $n → $K) := outerLast
  let mut prfE : Expr := q(List.ofFn_zero (f := fun i ↦ List.ofFn ($last0 i)))
  let mut tailE : Expr := outerLast
  let mut m : ℕ := 0
  for (rvec, entries, last) in (outerRows.zip rowData).reverse do
    let (xs, rprfE) := rowOfFnProof fieldInst entries last
    have m' : Q(ℕ) := mkRawNatLit m
    have rtail : Q(Fin $m' → Fin $n → $K) := tailE
    have rprf : Q(List.ofFn $rvec = List.map Rat.cast $xs) := rprfE
    have prf : Q(List.ofFn (fun i ↦ List.ofFn ($rtail i))
        = List.map (List.map Rat.cast) $lst) := prfE
    prfE := q(LUDet.list_ofFn_vecCons List.ofFn $rvec $rtail $rprf $prf)
    tailE := q(Matrix.vecCons $rvec $rtail)
    lst := q($xs :: $lst)
    m := m + 1
  return (lst, prfE)

/-- Evaluates `e` as a rational numeral, using `what` to identify an invalid expression. -/
def evalEntry {u : Level} (K : Q(Type u)) (fieldInst : Q(Field $K))
    (_charZeroInst : Q(CharZero $K)) (e : Q($K)) (what : MessageData) :
    MetaM (Entry K) := do
  let r ← try Mathlib.Meta.NormNum.derive (u := u) (α := K) e
    catch _ => throwError "lu_det: {what} is not a rational numeral: {e}"
  let some ⟨v, nE, dE, prf⟩ := r.toRat' q(inferInstance)
    | throwError "lu_det: {what} is not a rational numeral: {e}"
  return ⟨e, v, q(mkRat $nE $dE), q((mkRat $nE $dE : $K)),
    q(LUDet.eq_ratCast_of_isRat $prf)⟩

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
  let ⟨u, K, lhs⟩ ← inferTypeQ' lhs
  have d : Q($K) := d
  let ~q(@Matrix.det $ixType _ _ _ _ $M) := lhs
    | throwError "lu_det: goal is not of the form `Matrix.det M = d`"
  let ~q(Fin $nE) := (← whnfR ixType)
    | throwError "lu_det: the matrix is not indexed by `Fin n`"
  let some n ← getNatValue? nE
    | throwError "lu_det: matrix dimension is not a numeral"
  let fieldInst : Q(Field $K) ← synthInstanceQ q(Field $K)
  let charZeroInst : Q(CharZero $K) ← synthInstanceQ q(CharZero $K)
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
  let dres ← evalEntry K fieldInst charZeroInst d m!"the right-hand side"
  have dqE : Q(ℚ) := dres.lit
  let (luVals, swaps) := luDecompose vals
  let sign : ℚ := if swaps.length % 2 = 0 then 1 else -1
  let detVal : ℚ := (List.finRange n).foldl (fun acc i ↦ acc * luVals[i][i]) sign
  unless detVal = dres.val do
    throwError "lu_det: the determinant is {detVal}, but the goal claims {dres.val}"
  have lE : Q(List (List ℚ)) := toExpr <| List.ofFn fun i : Fin n ↦
    List.ofFn fun j : Fin (i.val + 1) ↦ if i.val = j.val then 1 else luVals[i][j.val]
  have vE : Q(List (List ℚ)) := toExpr <| List.ofFn fun i : Fin n ↦
    List.ofFn fun j : Fin (i.val + 1) ↦ luVals[j.val][i.val]
  have swapsE : Q(List (ℕ × ℕ)) := toExpr swaps
  let rowData := (entryRows.toArray.zip rowPeels).map fun (row, _, _, last) ↦ (row.toList, last)
  let (aE, hAExpr) := rowsOfFnProof fieldInst nE outerRows outerLast rowData
  have hA : Q((List.ofFn fun i ↦ List.ofFn fun j ↦ $M i j) = List.map (List.map (↑)) $aE) := hAExpr
  have hdK : Q($d = ($dqE : $K)) := dres.pf
  have hcert : Q(LUDet.checkCertificate $nE $aE $lE $vE $swapsE $dqE) := reflBoolTrue
  g.assign q(LUDet.det_eq_of_lu $M $aE $lE $vE $swapsE $dqE $d $hA $hcert $hdK)

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
