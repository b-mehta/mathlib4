/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.Data.List.Enum
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Support lemmas for the `lu_det` tactic

This file defines the certificate checkers used by `lu_det` and proves their correctness in
`LUDet.det_eq_of_lu`.
-/

namespace LUDet

open List

/-! ### Certificate checkers -/

@[expose] public section

/-- The dot product of the common prefix of two rows. -/
def dot : List ℚ → List ℚ → ℚ
  | x :: xs, y :: ys => x * y + dot xs ys
  | _, _ => 0

/-- Checks that `ar` contains the dot products of `lr` with the rows of `vRows`. -/
def rowMulEq (lr : List ℚ) (vRows : List (List ℚ)) (ar : List ℚ) : Bool :=
  all₂ (fun v a ↦ dot lr v = a) vRows ar

/-- Checks `lRows * vRowsᵀ = aRows`, interpreting each argument as a list of rows. -/
def checkMul (vRows lRows aRows : List (List ℚ)) : Bool :=
  all₂ (fun lr ar ↦ rowMulEq lr vRows ar) lRows aRows

/-- Checks that `rows` has `n` rows and row `i` has length `i + 1`. -/
def checkStair (n : ℕ) (rows : List (List ℚ)) : Bool :=
  rows.length = n && rows.zipIdx.all fun ri ↦ ri.1.length = ri.2 + 1

/-- The product of the last entry of each row, using `0` for an empty row. -/
def diagProd (rows : List (List ℚ)) : ℚ :=
  (rows.map fun r ↦ r.getLastD 0).prod

/-- Replaces rows `i` and `j` by the original rows `j` and `i`. An out-of-range source is
`[]`, and an out-of-range destination is ignored. -/
def swapRows (i j : ℕ) (rows : List (List ℚ)) : List (List ℚ) :=
  (rows.set i (rows[j]?.getD [])).set j (rows[i]?.getD [])

/-- Applies the row swaps from head to tail. -/
def applySwaps : List (ℕ × ℕ) → List (List ℚ) → List (List ℚ)
  | [], rows => rows
  | p :: s, rows => applySwaps s (swapRows p.1 p.2 rows)

end

/-! ### Correctness -/

/-- Read a list of rows as an `n × n` matrix; entries out of range are `0`. -/
def toMatrix {α : Type*} [Zero α] (n : ℕ) (rows : List (List α)) : Matrix (Fin n) (Fin n) α :=
  .of fun i j ↦ (rows[i]?.bind fun r ↦ r[j]?).getD 0

/-- Evaluation of `toMatrix`. -/
@[simp]
theorem toMatrix_apply {α : Type*} [Zero α] {n : ℕ} (rows : List (List α)) (i j : Fin n) :
    toMatrix n rows i j = (rows[i]?.bind fun r ↦ r[j]?).getD 0 :=
  rfl

/-- Characterization of successful `rowMulEq` checks. -/
theorem rowMulEq_iff {lr : List ℚ} {vs : List (List ℚ)} {ar : List ℚ} :
    rowMulEq lr vs ar ↔ ar = vs.map fun v ↦ dot lr v := by
  simp [rowMulEq, @eq_comm _ ar, ← forall₂_eq_eq_eq, forall₂_map_left_iff]

/-- Characterization of successful `checkMul` checks. -/
theorem checkMul_iff {vs ls as : List (List ℚ)} :
    checkMul vs ls as ↔ as = ls.map fun lr ↦ vs.map fun v ↦ dot lr v := by
  rw [checkMul, all₂_eq_true, eq_comm, ← forall₂_eq_eq_eq, forall₂_map_left_iff]
  grind [rowMulEq_iff]

/-- Characterization of successful `checkStair` checks. -/
theorem checkStair_iff {n : ℕ} {rows : List (List ℚ)} :
    checkStair n rows ↔
      rows.length = n ∧ ∀ t (ht : t < rows.length), rows[t].length = t + 1 := by
  simp only [checkStair, Bool.and_eq_true, decide_eq_true_eq, all_eq_true, forall_mem_zipIdx']

/-- Rows of length `i + 1` form a lower-triangular matrix under `toMatrix`. -/
theorem isLowerTriangular_toMatrix {n : ℕ} {rows : List (List ℚ)}
    (h : ∀ t (ht : t < rows.length), rows[t].length = t + 1) :
    Matrix.IsLowerTriangular (toMatrix n rows) := by
  intro i j hij
  grind [toMatrix_apply, OrderDual.toDual_lt_toDual, Fin.lt_def]

/-- `dot` as a `Finset.range` sum, padded with zeros up to `n`. -/
theorem dot_eq_sum {xs ys : List ℚ} {n : ℕ} (hx : xs.length ≤ n) (hy : ys.length ≤ n) :
    dot xs ys = ∑ k ∈ Finset.range n, xs[k]?.getD 0 * ys[k]?.getD 0 := by
  induction n generalizing xs ys with
  | zero => cases xs <;> simp_all [dot]
  | succ m ih =>
    cases xs with
    | nil => simp [dot]
    | cons x xs =>
      cases ys with
      | nil => simp [dot]
      | cons y ys =>
        rw [dot]
        grind [Finset.sum_range_succ']

/-- Expresses `List.ofFn` of a `Matrix.vecCons` as a list cons after applying `g`. -/
public theorem list_ofFn_vecCons {α β : Type*} (g : α → β) {m : ℕ} (x : α) (v : Fin m → α)
    {y : β} {ys : List β} (hy : g x = y) (h : ofFn (fun i ↦ g (v i)) = ys) :
    ofFn (fun i ↦ g (Matrix.vecCons x v i)) = y :: ys := by simp [← hy, ← h, ofFn_succ]

/-- Applying `toMatrix` to the `List.ofFn` representation of a matrix recovers it. -/
theorem toMatrix_ofFn {α : Type*} [Zero α] {n : ℕ} {M : Matrix (Fin n) (Fin n) α} :
    toMatrix n (ofFn fun i ↦ ofFn fun j ↦ M i j) = M := by
  ext i j
  simp [i.isLt, j.isLt]

/-- `toMatrix` commutes with mapping a zero-preserving function over the entries. -/
theorem toMatrix_map {α β : Type*} [Zero α] [Zero β] {f : α → β} (hf : f 0 = 0) {n : ℕ}
    {rows : List (List α)} :
    toMatrix n (rows.map (List.map f)) = (toMatrix n rows).map f := by
  ext i j
  grind [toMatrix_apply, Matrix.map_apply]

/-- `swapRows` reads back as precomposition with `Equiv.swap`. -/
theorem toMatrix_swapRows {n : ℕ} {rows : List (List ℚ)} (hlen : rows.length = n)
    {i j : ℕ} (hi : i < n) (hj : j < n) :
    toMatrix n (swapRows i j rows)
      = (toMatrix n rows).submatrix (Equiv.swap ⟨i, hi⟩ ⟨j, hj⟩) id := by
  ext a b
  grind [toMatrix_apply, Matrix.submatrix_apply, swapRows, List.length_set,
    List.getElem?_eq_getElem, Fin.ext_iff]

/-- One row swap negates the determinant. -/
theorem det_toMatrix_swapRows {n : ℕ} {rows : List (List ℚ)} (hlen : rows.length = n)
    {i j : ℕ} (hi : i < n) (hj : j < n) (hij : i ≠ j) :
    (toMatrix n (swapRows i j rows)).det = -(toMatrix n rows).det := by
  rw [toMatrix_swapRows hlen hi hj, Matrix.det_permute,
    Equiv.Perm.sign_swap (by simpa [Fin.ext_iff] using hij)]
  norm_num

/-- Each row swap contributes a factor `-1` to the determinant. -/
theorem det_toMatrix_applySwaps {n : ℕ} {swaps : List (ℕ × ℕ)} {rows : List (List ℚ)}
    (hlen : rows.length = n) (hok : swaps.all fun p ↦ p.1 < p.2 && p.2 < n) :
    (toMatrix n (applySwaps swaps rows)).det
      = (-1) ^ swaps.length * (toMatrix n rows).det := by
  induction swaps generalizing rows with
  | nil => simp [applySwaps]
  | cons p s ih =>
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hok
    simp only [applySwaps]
    rw [ih (by simp [swapRows, hlen]) hok.2,
      det_toMatrix_swapRows hlen (hok.1.1.trans hok.1.2) hok.1.2 hok.1.1.ne]
    grind [pow_succ]

/-- For rows of length `i + 1`, `diagProd` is the diagonal product of `toMatrix`. -/
theorem diagProd_eq {n : ℕ} {rows : List (List ℚ)} (hlen : rows.length = n)
    (hrows : ∀ t (ht : t < rows.length), rows[t].length = t + 1) :
    diagProd rows = ∏ i : Fin n, toMatrix n rows i i := by
  subst hlen
  rw [diagProd, ← prod_ofFn]
  congr 1
  apply ext_getElem <;> grind [toMatrix_apply]

/-- Computes the determinant from rows accepted by `checkStair` and `checkMul`, accounting for
the row swaps. -/
theorem det_toMatrix_eq {n : ℕ} {aRows lRows vRows : List (List ℚ)}
    {swaps : List (ℕ × ℕ)} (hAlen : aRows.length = n)
    (hswaps : swaps.all fun p ↦ p.1 < p.2 && p.2 < n)
    (hsL : checkStair n lRows)
    (hsV : checkStair n vRows)
    (hmul : checkMul vRows lRows (applySwaps swaps aRows)) :
    (toMatrix n aRows).det = (-1) ^ swaps.length * (diagProd lRows * diagProd vRows) := by
  obtain ⟨hLlen, hLrows⟩ := checkStair_iff.mp hsL
  obtain ⟨hVlen, hVrows⟩ := checkStair_iff.mp hsV
  have hAeq := checkMul_iff.mp hmul
  have hM : toMatrix n (applySwaps swaps aRows)
      = toMatrix n lRows * (toMatrix n vRows).transpose := by
    ext i j
    have hilt : i < lRows.length := by grind
    have hjlt : j < vRows.length := by grind
    have hdot : ((applySwaps swaps aRows)[i]?.bind fun r ↦ r[j]?).getD 0
        = dot lRows[i] vRows[j] := by simp [hAeq, hilt, hjlt]
    have hxlen : lRows[i].length ≤ n := by grind
    have hylen : vRows[j].length ≤ n := by grind
    rw [Matrix.mul_apply]
    simp only [Matrix.transpose_apply, toMatrix_apply]
    rw [hdot, dot_eq_sum hxlen hylen, ← Fin.sum_univ_eq_sum_range]
    simp [hilt, hjlt]
  have h2 := det_toMatrix_applySwaps hAlen hswaps
  rw [hM, Matrix.det_mul, Matrix.det_transpose,
    Matrix.det_of_isLowerTriangular _ (isLowerTriangular_toMatrix hLrows),
    Matrix.det_of_isLowerTriangular _ (isLowerTriangular_toMatrix hVrows),
    ← diagProd_eq hLlen hLrows, ← diagProd_eq hVlen hVrows] at h2
  rw [h2, ← mul_assoc, ← mul_pow]
  simp

/-- A successful LU certificate for `M` proves `M.det = d`. -/
public theorem det_eq_of_lu {K : Type*} [Field K] [CharZero K] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K)
    (aRows lRows vRows : List (List ℚ)) (swaps : List (ℕ × ℕ)) (dq : ℚ) (d : K)
    (hA : (ofFn fun i ↦ ofFn fun j ↦ M i j) = aRows.map (List.map Rat.cast))
    (hswaps : swaps.all fun p ↦ p.1 < p.2 && p.2 < n)
    (hsL : checkStair n lRows)
    (hsV : checkStair n vRows)
    (hmul : checkMul vRows lRows (applySwaps swaps aRows))
    (hd : diagProd lRows * diagProd vRows == bif (swaps.length % 2).beq 1 then -dq else dq)
    (hdK : d = (dq : K)) :
    M.det = d := by
  have hsgn : (-1) ^ swaps.length * (diagProd lRows * diagProd vRows) = dq := by
    rcases Nat.even_or_odd swaps.length with h | h <;>
      simp_all [of_decide_eq_true hd, Nat.even_iff, Nat.odd_iff, Odd.neg_one_pow, Nat.beq]
  have hAlen : aRows.length = n := by simpa using (congrArg List.length hA).symm
  have hMA : M = (Rat.castHom K).mapMatrix (toMatrix n aRows) := by
    rw [RingHom.mapMatrix_apply, Rat.coe_castHom,
      ← toMatrix_map Rat.cast_zero, ← hA, toMatrix_ofFn]
  rwa [hMA, ← RingHom.map_det, det_toMatrix_eq hAlen hswaps hsL hsV hmul, hsgn, eq_comm]

end LUDet
