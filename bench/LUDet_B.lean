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

`lu_det` proves goals of the form `Matrix.det !![...] = d` over any field of
characteristic zero, as long as the entries are rational numerals. The LU decomposition
is computed during elaboration; the kernel re-checks everything from scratch, over ℚ,
using the checkers from `Mathlib.LinearAlgebra.Matrix.Determinant.LU`.
-/

public section

namespace Mathlib.Tactic.LUDet

/-- What `norm_num`'s `IsRat` certificate says, as an equality with a cast rational. -/
theorem eq_ratCast_of_isRat {K : Type*} [DivisionRing K] [CharZero K] {e : K} {n : ℤ}
    {d : ℕ} (h : Mathlib.Meta.NormNum.IsRat e n d) : e = ((mkRat n d : ℚ) : K) := by
  obtain ⟨inv, rfl⟩ := h
  rw [Rat.mkRat_eq_div, Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast,
    div_eq_mul_inv, invOf_eq_inv]

end Mathlib.Tactic.LUDet

end

meta section

open Lean Elab Meta Qq

namespace Mathlib.Tactic.LUDet

/-- Gaussian elimination on the row-major `n × n` matrix `A`: a unit lower triangular
`L`, an upper triangular `U` and a list of row swaps such that `L * U` is `A` with those
swaps applied. A zero pivot gets swapped with a later row when possible; when the rest
of the column is zero too, the pivot stays zero and the matrix is singular. -/
def luDecompose {n : ℕ} (A : Vector (Vector ℚ n) n) :
    Vector (Vector ℚ n) n × Vector (Vector ℚ n) n × List (ℕ × ℕ) := Id.run do
  let mut W := A
  let mut L : Vector (Vector ℚ n) n := .replicate n (.replicate n 0)
  let mut swaps : Array (ℕ × ℕ) := #[]
  for h : k in [0:n] do
    have hk : k < n := h.upper
    if W[k][k] = 0 then
      if let some p := (List.finRange n).find? fun p ↦ decide (k < p.val ∧ W[p][k] ≠ 0) then
        swaps := swaps.push (k, p.val)
        W := W.swap k p.val
        -- before step `k` the multipliers sit in columns below `k`, so whole rows swap
        L := L.swap k p.val
    let pivot := W[k][k]
    unless pivot = 0 do
      for h' : i in [k+1:n] do
        have hi : i < n := h'.upper
        let f := W[i][k] / pivot
        L := L.set i (L[i].set k f)
        for h'' : j in [k:n] do
          have hj : j < n := h''.upper
          W := W.set i (W[i].set j (W[i][j] - f * W[k][j]))
  for h : i in [0:n] do
    have hi : i < n := h.upper
    L := L.set i (L[i].set i 1)
  return (L, W, swaps.toList)

/-- The `norm_num` evaluation of a rational numeral `e : K`: its value, its literal in
`mkRat` shape, the literal's cast into `K`, and a proof that `e` equals the cast. -/
structure EntryResult {u : Level} (K : Q(Type u)) (e : Q($K)) where
  val : ℚ
  lit : Q(ℚ)
  cast : Q($K)
  pf : Q($e = $cast)

/-- One entry of the matrix literal: the entry as written, the `Matrix.vecCons` tail
after it, and its `norm_num` evaluation. -/
structure Entry {u : Level} (K : Q(Type u)) where
  x : Q($K)
  tail : Expr
  res : EntryResult K x

/-- Strip a chain of `Matrix.vecCons` applications with entries of type `α`, returning
each entry together with the tail after it, plus the final `Fin 0 → _` tail. -/
partial def peelVec {u : Level} (α : Q(Type u)) (e : Expr) :
    MetaM (List (Q($α) × Expr) × Expr) := do
  let e' ← whnfR e
  match_expr e' with
  | Matrix.vecCons _ _ x xs =>
    let (pairs, last) ← peelVec α xs
    have x : Q($α) := x
    return ((x, xs) :: pairs, last)
  | _ => return ([], e')

/-- For one row `v` of the literal, build the list `xs` of the casts of its entries
together with a proof that `List.ofFn v = xs`, one `LUDet.list_ofFn_vecCons` (at
`g := id`) per entry. -/
def rowOfFnProof {u : Level} {K : Q(Type u)} (entries : List (Entry K)) (finalTail : Expr) :
    Q(List $K) × Expr :=
  have tail0 : Q(Fin 0 → $K) := finalTail
  let base : Q(List $K) × Expr × ℕ := (q([]), q(List.ofFn_zero (f := $tail0)), 0)
  let (lst, prf, _) := entries.foldr
    (fun e (acc : Q(List $K) × Expr × ℕ) ↦
      let (lst, prfE, m) := acc
      have x : Q($K) := e.x
      have y : Q($K) := e.res.cast
      have hy : Q($x = $y) := e.res.pf
      have m' : Q(ℕ) := mkRawNatLit m
      have tail : Q(Fin $m' → $K) := e.tail
      have prf : Q(List.ofFn $tail = $lst) := prfE
      (q($y :: $lst), q(LUDet.list_ofFn_vecCons id $x $tail $hy $prf), m + 1))
    base
  (lst, prf)

/-- Same as `rowOfFnProof`, one level up: the list of all the rows, with a proof that
it reflects the whole literal, via `LUDet.list_ofFn_vecCons` at `g := List.ofFn`. -/
def rowsOfFnProof {u : Level} {K : Q(Type u)} (n : Q(ℕ))
    (outerPairs : Array (Q(Fin $n → $K) × Expr)) (outerLast : Expr)
    (rowData : Array (List (Entry K) × Expr)) :
    Q(List (List $K)) × Expr := Id.run do
  let mut lst : Q(List (List $K)) := q([])
  have last0 : Q(Fin 0 → Fin $n → $K) := outerLast
  let mut prfE : Expr := q(List.ofFn_zero (f := fun i ↦ List.ofFn ($last0 i)))
  let mut m : ℕ := 0
  for ((rvec, rtailE), entries, last) in (outerPairs.zip rowData).reverse do
    let (xs, rprfE) := rowOfFnProof entries last
    have m' : Q(ℕ) := mkRawNatLit m
    have rtail : Q(Fin $m' → Fin $n → $K) := rtailE
    have rprf : Q(List.ofFn $rvec = $xs) := rprfE
    have prf : Q(List.ofFn (fun i ↦ List.ofFn ($rtail i)) = $lst) := prfE
    prfE := q(LUDet.list_ofFn_vecCons List.ofFn $rvec $rtail $rprf $prf)
    lst := q($xs :: $lst)
    m := m + 1
  return (lst, prfE)

/-- Evaluate an expression to a rational numeral using `norm_num`. -/
def evalEntry {u : Level} (K : Q(Type u)) (_fieldInst : Q(Field $K))
    (_charZeroInst : Q(CharZero $K)) (e : Q($K)) (what : MessageData) :
    MetaM (EntryResult K e) := do
  let r ← try Mathlib.Meta.NormNum.derive (u := u) (α := K) e
    catch _ => throwError "lu_det: {what} is not a rational numeral: {e}"
  let some ⟨v, nE, dE, prf⟩ := r.toRat' q(inferInstance)
    | throwError "lu_det: {what} is not a rational numeral: {e}"
  return ⟨v, q(mkRat $nE $dE), q(((mkRat $nE $dE : ℚ) : $K)),
    q(LUDet.eq_ratCast_of_isRat $prf)⟩

/-- Reinterpret `a` as a vector of length `n`; the matrix shape guard. -/
def toVectorOfLen {α : Type} (n : ℕ) (a : Array α) : MetaM (Vector α n) := do
  if h : a.size = n then return a.toVector.cast h
  else throwError "lu_det: matrix is not a `!![...]` literal"

/-- Prove a goal of the form `Matrix.det !![...] = d` by handing the kernel an LU
certificate. -/
def luDetTactic (g : MVarId) : MetaM Unit := do
  let tgt : Q(Prop) ← instantiateMVars (← g.getType)
  let_expr Eq _ lhs d := tgt
    | throwError "lu_det: goal is not of the form `Matrix.det M = d`"
  let_expr Matrix.det ixType _deq _ft K _cr M := lhs
    | throwError "lu_det: goal is not of the form `Matrix.det M = d`"
  let_expr Fin n := (← whnfR ixType)
    | throwError "lu_det: the matrix is not indexed by `Fin n`"
  have n : Q(ℕ) := n
  let some dim ← getNatValue? n
    | throwError "lu_det: matrix dimension is not a numeral"
  let u ← getDecLevel K
  have K : Q(Type u) := K
  let _fieldInst : Q(Field $K) ← synthInstanceQ q(Field $K)
  let _charZeroInst : Q(CharZero $K) ← synthInstanceQ q(CharZero $K)
  have M : Q(Matrix (Fin $n) (Fin $n) $K) := M
  have d : Q($K) := d
  -- peel the `!![...]` literal once; the pieces feed both the entry evaluation and the
  -- reflection proof
  let ~q(Matrix.of $rowsVec) := M
    | throwError "lu_det: matrix is not a `!![...]` literal"
  let (outerPairs, outerLast) ← peelVec q(Fin $n → $K) rowsVec
  let outerPairs := outerPairs.toArray
  let rowPeels ← outerPairs.mapM fun (rvec, _) ↦ peelVec K rvec
  -- each entry becomes its value together with the pieces of `hA`: the `mkRat` literal
  -- for the checkers, its cast into `K`, and the norm_num proof the entry equals it
  let entryRows : Array (Array (Entry K)) ← rowPeels.mapIdxM fun i (pairs, _) ↦
    pairs.toArray.mapIdxM fun j (x, tail) ↦ do
      return ⟨x, tail, ← evalEntry K _fieldInst _charZeroInst x m!"matrix entry ({i}, {j})"⟩
  let entryRows : Vector (Vector (Entry K) dim) dim ←
    toVectorOfLen dim (← entryRows.mapM (toVectorOfLen dim))
  let vals := entryRows.map (·.map (·.res.val))
  let dres ← evalEntry K _fieldInst _charZeroInst d m!"the right-hand side"
  have dqE : Q(ℚ) := dres.lit
  let (lVals, uVals, swaps) := luDecompose vals
  let sign : ℚ := if swaps.length % 2 = 0 then 1 else -1
  -- `L` has unit diagonal, so the determinant is the sign times the `U` diagonal product
  let detVal := (List.finRange dim).foldl (fun acc i ↦ acc * uVals[i][i]) sign
  unless detVal = dres.val do
    throwError "lu_det: the determinant is {detVal}, but the goal claims {dres.val}"
  -- both factors are emitted as staircases: row `i` keeps only its first `i + 1`
  -- entries, and the missing ones mean `0`
  have lE : Q(List (List ℚ)) := toExpr <| List.ofFn fun i : Fin dim ↦
    List.ofFn fun j : Fin (i.val + 1) ↦ lVals[i][j.val]
  -- `V` is `Uᵀ`, so every entry of the product is a dot product of two rows
  have vE : Q(List (List ℚ)) := toExpr <| List.ofFn fun i : Fin dim ↦
    List.ofFn fun j : Fin (i.val + 1) ↦ uVals[j.val][i.val]
  have swapsE : Q(List (ℕ × ℕ)) := toExpr swaps
  -- the checkers work on the `mkRat` literals; `hA` relates the goal's literal to their
  -- casts, one lemma application per cons
  let aRowLits ← entryRows.toList.mapM fun row ↦ mkListLit q(ℚ) (row.toList.map (·.res.lit))
  have aE : Q(List (List ℚ)) := ← mkListLit q(List ℚ) aRowLits
  let rowData := (entryRows.toArray.zip rowPeels).map fun (row, _, last) ↦ (row.toList, last)
  let (_, hAExpr) := rowsOfFnProof n outerPairs outerLast rowData
  have hA : Q((List.ofFn fun i : Fin $n ↦ List.ofFn fun j : Fin $n ↦ $M i j)
      = List.map (List.map Rat.cast) $aE) := hAExpr
  have hdK : Q((($dqE : ℚ) : $K) = $d) := (← mkEqSymm dres.pf)
  have hswaps : Q((List.all $swapsE fun p ↦ p.1 < p.2 && p.2 < $n) = true) := reflBoolTrue
  have hsL : Q(LUDet.checkStair $n $lE = true) := reflBoolTrue
  have hsV : Q(LUDet.checkStair $n $vE = true) := reflBoolTrue
  have hmul : Q(LUDet.checkMul $vE $lE (LUDet.applySwaps $swapsE $aE) = true) :=
    reflBoolTrue
  have hd : Q(((LUDet.diagProd $lE) * LUDet.diagProd $vE
      == bif ((List.length $swapsE) % 2).beq 1 then -$dqE else $dqE) = true) := reflBoolTrue
  g.assign
    q(LUDet.det_eq_of_lu $M $aE $lE $vE $swapsE $dqE $d $hA $hswaps $hsL $hsV $hmul $hd
      $hdK)

/--
`lu_det` proves goals of the form `Matrix.det !![...] = d`, where the matrix lives in a
field of characteristic zero and its entries are rational numerals, by computing an LU
decomposition and letting the kernel check it.

```lean
example : Matrix.det (R := ℝ) !![1, 2; 3, 4] = -2 := by lu_det
```
-/
elab "lu_det" : tactic => Tactic.liftMetaFinishingTactic luDetTactic

end Mathlib.Tactic.LUDet

end
