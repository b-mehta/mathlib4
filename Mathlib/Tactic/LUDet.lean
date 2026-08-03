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

/-- The value and certificate obtained by evaluating `e` as a rational numeral. -/
structure EntryResult {u : Level} (K : Q(Type u)) (e : Q($K)) where
  val : ℚ
  lit : Q(ℚ)
  cast : Q($K)
  pf : Q($e = $cast)

/-- A matrix entry, its remaining `Matrix.vecCons` tail, and its rational evaluation. -/
structure Entry {u : Level} (K : Q(Type u)) where
  x : Q($K)
  tail : Expr
  res : EntryResult K x

/-- Decomposes a `Matrix.vecCons` chain into entries paired with their remaining tails,
followed by the final tail. -/
partial def peelVec {u : Level} (α : Q(Type u)) (e : Expr) :
    MetaM (List (Q($α) × Expr) × Expr) := do
  let e' ← whnfR e
  match_expr e' with
  | Matrix.vecCons _ _ x xs =>
    let (pairs, last) ← peelVec α xs
    have x : Q($α) := x
    return ((x, xs) :: pairs, last)
  | _ => return ([], e')

/-- Builds rational entries and proves that casting them gives the reflected row. -/
def rowOfFnProof {u : Level} {K : Q(Type u)} (fieldInst : Q(Field $K))
    (entries : List (Entry K)) (finalTail : Expr) :
    Q(List ℚ) × Expr :=
  have tail0 : Q(Fin 0 → $K) := finalTail
  let base : Q(List ℚ) × Expr × ℕ := (q([]), q(List.ofFn_zero (f := $tail0)), 0)
  let (lst, prf, _) := entries.foldr
    (fun e acc ↦
      let (lst, prfE, m) := acc
      have x : Q($K) := e.x
      have y : Q(ℚ) := e.res.lit
      have yK : Q($K) := e.res.cast
      have hy : Q($x = $yK) := e.res.pf
      have m' : Q(ℕ) := mkRawNatLit m
      have tail : Q(Fin $m' → $K) := e.tail
      have prf : Q(List.ofFn $tail = List.map Rat.cast $lst) := prfE
      (q($y :: $lst), q(LUDet.list_ofFn_vecCons id $x $tail $hy $prf), m + 1))
    base
  (lst, prf)

/-- Builds rational rows and proves that casting their entries gives the reflected matrix. -/
def rowsOfFnProof {u : Level} {K : Q(Type u)} (fieldInst : Q(Field $K)) (n : Q(ℕ))
    (outerPairs : Array (Q(Fin $n → $K) × Expr)) (outerLast : Expr)
    (rowData : Array (List (Entry K) × Expr)) :
    Q(List (List ℚ)) × Expr := Id.run do
  let mut lst : Q(List (List ℚ)) := q([])
  have last0 : Q(Fin 0 → Fin $n → $K) := outerLast
  let mut prfE : Expr := q(List.ofFn_zero (f := fun i ↦ List.ofFn ($last0 i)))
  let mut m : ℕ := 0
  for ((rvec, rtailE), entries, last) in (outerPairs.zip rowData).reverse do
    let (xs, rprfE) := rowOfFnProof fieldInst entries last
    have m' : Q(ℕ) := mkRawNatLit m
    have rtail : Q(Fin $m' → Fin $n → $K) := rtailE
    have rprf : Q(List.ofFn $rvec = List.map Rat.cast $xs) := rprfE
    have prf : Q(List.ofFn (fun i ↦ List.ofFn ($rtail i))
        = List.map (List.map Rat.cast) $lst) := prfE
    prfE := q(LUDet.list_ofFn_vecCons List.ofFn $rvec $rtail $rprf $prf)
    lst := q($xs :: $lst)
    m := m + 1
  return (lst, prfE)

/-- Evaluates `e` as a rational numeral, using `what` to identify an invalid expression. -/
def evalEntry {u : Level} (K : Q(Type u)) (fieldInst : Q(Field $K))
    (_charZeroInst : Q(CharZero $K)) (e : Q($K)) (what : MessageData) :
    MetaM (EntryResult K e) := do
  let r ← try Mathlib.Meta.NormNum.derive (u := u) (α := K) e
    catch _ => throwError "lu_det: {what} is not a rational numeral: {e}"
  let some ⟨v, nE, dE, prf⟩ := r.toRat' q(inferInstance)
    | throwError "lu_det: {what} is not a rational numeral: {e}"
  return ⟨v, q(mkRat $nE $dE), q((mkRat $nE $dE : $K)),
    q(LUDet.eq_ratCast_of_isRat $prf)⟩

/-- Converts `a` to a vector of length `n`, reporting an invalid matrix literal on mismatch. -/
def toVectorOfLen {α : Type} (n : ℕ) (a : Array α) : MetaM (Vector α n) := do
  if h : a.size = n then return a.toVector.cast h
  else throwError "lu_det: matrix is not a `!![...]` literal"

/-- Closes `Matrix.det !![...] = d` when the field has characteristic zero and all displayed
values are rational numerals. -/
def luDetTactic (g : MVarId) : MetaM Unit := do
  let tgt : Q(Prop) ← instantiateMVars (← g.getType)
  let_expr Eq _ lhs d := tgt
    | throwError "lu_det: goal is not of the form `Matrix.det M = d`"
  let_expr Matrix.det ixType _ _ K _ M := lhs
    | throwError "lu_det: goal is not of the form `Matrix.det M = d`"
  let_expr Fin n := (← whnfR ixType)
    | throwError "lu_det: the matrix is not indexed by `Fin n`"
  have n : Q(ℕ) := n
  let some dim ← getNatValue? n
    | throwError "lu_det: matrix dimension is not a numeral"
  let u ← getDecLevel K
  have K : Q(Type u) := K
  let fieldInst : Q(Field $K) ← synthInstanceQ q(Field $K)
  let charZeroInst : Q(CharZero $K) ← synthInstanceQ q(CharZero $K)
  have M : Q(Matrix (Fin $n) (Fin $n) $K) := M
  have d : Q($K) := d
  let ~q(Matrix.of $rowsVec) := M
    | throwError "lu_det: matrix is not a `!![...]` literal"
  let (outerPairs, outerLast) ← peelVec q(Fin $n → $K) rowsVec
  let outerPairs := outerPairs.toArray
  let rowPeels ← outerPairs.mapM fun (rvec, _) ↦ peelVec K rvec
  let entryRows : Array (Array (Entry K)) ← rowPeels.mapIdxM fun i (pairs, _) ↦
    pairs.toArray.mapIdxM fun j (x, tail) ↦ do
      return ⟨x, tail, ← evalEntry K fieldInst charZeroInst x m!"matrix entry ({i}, {j})"⟩
  let entryRows : Vector (Vector (Entry K) dim) dim ←
    toVectorOfLen dim (← entryRows.mapM (toVectorOfLen dim))
  let vals := entryRows.map (·.map (·.res.val))
  let dres ← evalEntry K fieldInst charZeroInst d m!"the right-hand side"
  have dqE : Q(ℚ) := dres.lit
  let (luVals, swaps) := luDecompose vals
  let sign : ℚ := if swaps.length % 2 = 0 then 1 else -1
  let detVal := (List.finRange dim).foldl (fun acc i ↦ acc * luVals[i][i]) sign
  unless detVal = dres.val do
    throwError "lu_det: the determinant is {detVal}, but the goal claims {dres.val}"
  have lE : Q(List (List ℚ)) := toExpr <| List.ofFn fun i : Fin dim ↦
    List.ofFn fun j : Fin (i.val + 1) ↦ if i.val = j.val then 1 else luVals[i][j.val]
  have vE : Q(List (List ℚ)) := toExpr <| List.ofFn fun i : Fin dim ↦
    List.ofFn fun j : Fin (i.val + 1) ↦ luVals[j.val][i.val]
  have swapsE : Q(List (ℕ × ℕ)) := toExpr swaps
  let rowData := (entryRows.toArray.zip rowPeels).map fun (row, _, last) ↦ (row.toList, last)
  let (aE, hAExpr) := rowsOfFnProof fieldInst n outerPairs outerLast rowData
  have hA : Q((List.ofFn fun i : Fin $n ↦ List.ofFn fun j : Fin $n ↦ $M i j)
      = List.map (List.map Rat.cast) $aE) := hAExpr
  have hdK : Q($d = ($dqE : $K)) := dres.pf
  have hswaps : Q(List.all $swapsE fun p ↦ p.1 < p.2 && p.2 < $n) := reflBoolTrue
  have hsL : Q(LUDet.checkStair $n $lE) := reflBoolTrue
  have hsV : Q(LUDet.checkStair $n $vE) := reflBoolTrue
  have hmul : Q(LUDet.checkMul $vE $lE (LUDet.applySwaps $swapsE $aE)) :=
    reflBoolTrue
  have hd : Q(((LUDet.diagProd $lE) * LUDet.diagProd $vE
      == bif ((List.length $swapsE) % 2).beq 1 then -$dqE else $dqE)) := reflBoolTrue
  g.assign
    q(LUDet.det_eq_of_lu $M $aE $lE $vE $swapsE $dqE $d $hA $hswaps $hsL $hsV $hmul $hd
      $hdK)

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
