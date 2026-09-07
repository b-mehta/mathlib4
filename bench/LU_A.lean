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
# Certificates for `lu_det`

The theorem `LUDet.det_eq_of_lu` verifies the LU certificate produced by `lu_det`.
-/

namespace LUDet

open List Matrix

/-! ### Certificate checkers -/

@[expose] public section

/-- The dot product of two lists, stopping when either list ends. -/
def dot : List ℚ → List ℚ → ℚ
  | x :: xs, y :: ys => x * y + dot xs ys
  | _, _ => 0

/-- Checks the matrix identity represented by `lRows * vRowsᵀ = aRows`. -/
def checkMul (vRows lRows aRows : List (List ℚ)) : Bool :=
  all₂ (fun lr ar ↦ all₂ (fun v a ↦ dot lr v = a) vRows ar) lRows aRows

/-- Checks that `rows` has `n` rows and row `i` has length `i + 1`. -/
def checkStair (n : ℕ) (rows : List (List ℚ)) : Bool :=
  rows.length = n && rows.zipIdx.all fun ri ↦ ri.1.length = ri.2 + 1

/-- The product of the last entry of each row, using `0` for an empty row. -/
def diagProd (rows : List (List ℚ)) : ℚ :=
  (rows.map fun r ↦ r.getLastD 0).prod

/-- Swap rows `i` and `j`, using `[]` when either row is missing. -/
def swapRows (i j : ℕ) (rows : List (List ℚ)) : List (List ℚ) :=
  (rows.set i (rows[j]?.getD [])).set j (rows[i]?.getD [])

/-- Apply the listed row swaps in order. -/
def applySwaps : List (ℕ × ℕ) → List (List ℚ) → List (List ℚ)
  | [], rows => rows
  | (i, j) :: s, rows => applySwaps s (swapRows i j rows)

/-- Checks an LU certificate over `ℚ`. -/
def checkCertificate (n : ℕ) (aRows lRows vRows : List (List ℚ))
    (swaps : List (ℕ × ℕ)) (dq : ℚ) : Bool :=
  swaps.all (fun p ↦ p.1 < p.2 && p.2 < n) &&
    (checkStair n lRows && (checkStair n vRows &&
      (checkMul vRows lRows (applySwaps swaps aRows) &&
        diagProd lRows * diagProd vRows == if Even swaps.length then dq else -dq)))

end

/-! ### Correctness -/

section ToMatrix

variable {α : Type*} [Zero α] {n : ℕ}

/-- Read a list of rows as an `n × n` matrix; entries out of range are `0`. -/
def toMatrix (n : ℕ) (rows : List (List α)) : Matrix (Fin n) (Fin n) α :=
  Matrix.of fun i j ↦ (rows[i]?.bind fun r ↦ r[j]?).getD 0

/-- `toMatrix` reads the `(i, j)` entry of `rows`, defaulting to `0`. -/
@[simp, grind =]
theorem toMatrix_apply (rows : List (List α)) (i j : Fin n) :
    toMatrix n rows i j = (rows[i]?.bind fun r ↦ r[j]?).getD 0 :=
  rfl

/-- Reading the rows of a matrix with `toMatrix` recovers the matrix. -/
theorem toMatrix_ofFn {M : Matrix (Fin n) (Fin n) α} :
    toMatrix n (ofFn fun i ↦ ofFn fun j ↦ M i j) = M := by
  ext i j
  grind

variable {β : Type*} [Zero β]

/-- `toMatrix` commutes with a map that preserves `0`. -/
theorem toMatrix_map {f : α → β} (hf : f 0 = 0) {rows : List (List α)} :
    toMatrix n (rows.map (List.map f)) = (toMatrix n rows).map f := by
  ext i j
  grind [map_apply]

end ToMatrix

section CheckerSpecs

variable {vs : List (List ℚ)}

/-- `checkMul vs ls as` holds exactly when `as` represents `ls * vsᵀ`. -/
theorem checkMul_iff {ls as : List (List ℚ)} :
    checkMul vs ls as ↔ as = ls.map fun lr ↦ vs.map fun v ↦ dot lr v := by
  simp [checkMul, eq_comm (a := as), ← forall₂_eq_eq_eq, forall₂_map_left_iff]

variable {n : ℕ} {rows : List (List ℚ)}

/-- `checkStair n rows` holds exactly when there are `n` rows and row `i` has length `i + 1`. -/
theorem checkStair_iff :
    checkStair n rows ↔ rows.length = n ∧ ∀ t (ht : t < rows.length), rows[t].length = t + 1 := by
  simp only [checkStair, Bool.and_eq_true, decide_eq_true_eq, all_eq_true, forall_mem_zipIdx']

/-- A list whose row `i` has length `i + 1` represents a lower-triangular matrix. -/
theorem isLowerTriangular_toMatrix
    (h : ∀ t (ht : t < rows.length), rows[t].length = t + 1) :
    IsLowerTriangular (toMatrix n rows) := by
  intro i j hij
  grind [OrderDual.toDual_lt_toDual]

/-- If row `i` has length `i + 1`, `diagProd` is the diagonal product of `toMatrix`. -/
theorem diagProd_eq (hlen : rows.length = n)
    (hrows : ∀ t (ht : t < rows.length), rows[t].length = t + 1) :
    diagProd rows = ∏ i : Fin n, toMatrix n rows i i := by
  rw [diagProd, ← prod_ofFn]
  congr 1
  apply ext_getElem <;> grind

end CheckerSpecs

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

section RowSwaps

variable {n : ℕ} {rows : List (List ℚ)}

/-- `swapRows` reads back as precomposition with `Equiv.swap`. -/
theorem toMatrix_swapRows (hlen : rows.length = n) {i j : ℕ} (hi : i < n) (hj : j < n) :
    toMatrix n (swapRows i j rows)
      = (toMatrix n rows).submatrix (Equiv.swap ⟨i, hi⟩ ⟨j, hj⟩) id := by
  ext a b
  grind [submatrix_apply, swapRows]

/-- One row swap negates the determinant. -/
theorem det_toMatrix_swapRows (hlen : rows.length = n) {i j : ℕ}
    (hi : i < n) (hj : j < n) (hij : i ≠ j) :
    (toMatrix n (swapRows i j rows)).det = -(toMatrix n rows).det := by
  rw [toMatrix_swapRows hlen hi hj, det_permute, Equiv.Perm.sign_swap (by grind)]
  simp

/-- Each row swap contributes a factor `-1` to the determinant. -/
theorem det_toMatrix_applySwaps {swaps : List (ℕ × ℕ)}
    (hlen : rows.length = n) (hok : swaps.all fun p ↦ p.1 < p.2 && p.2 < n) :
    (toMatrix n (applySwaps swaps rows)).det
      = (-1) ^ swaps.length * (toMatrix n rows).det := by
  induction swaps generalizing rows with
  | nil => simp [applySwaps]
  | cons p s ih =>
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hok
    simp only [applySwaps]
    rw [ih (by grind [swapRows]) hok.2, det_toMatrix_swapRows hlen (by grind) hok.1.2 hok.1.1.ne]
    grind

end RowSwaps

section Determinant

variable {n : ℕ} {aRows lRows vRows : List (List ℚ)} {swaps : List (ℕ × ℕ)}

/-- If two staircase matrices multiply to a row permutation of `aRows`, their diagonal
products give its determinant, with one sign change per row swap. -/
theorem det_toMatrix_eq (hAlen : aRows.length = n)
    (hswaps : swaps.all fun p ↦ p.1 < p.2 && p.2 < n)
    (hsL : checkStair n lRows) (hsV : checkStair n vRows)
    (hmul : checkMul vRows lRows (applySwaps swaps aRows)) :
    (toMatrix n aRows).det = (-1) ^ swaps.length * (diagProd lRows * diagProd vRows) := by
  obtain ⟨hLlen, hLrows⟩ := checkStair_iff.mp hsL
  obtain ⟨hVlen, hVrows⟩ := checkStair_iff.mp hsV
  rw [checkMul_iff] at hmul
  have hLU : toMatrix n (applySwaps swaps aRows) = toMatrix n lRows * (toMatrix n vRows)ᵀ := by
    ext i j
    have hlen : lRows[i].length ≤ n := by grind
    have hdot :
        ((applySwaps swaps aRows)[i]?.bind fun r ↦ r[j]?).getD 0 = dot lRows[i] vRows[j] := by
      grind
    simp only [mul_apply, transpose_apply, toMatrix_apply]
    rw [hdot, dot_eq_sum hlen (by grind), ← Fin.sum_univ_eq_sum_range]
    grind
  have hdetLU : (toMatrix n (applySwaps swaps aRows)).det = diagProd lRows * diagProd vRows := by
    rw [hLU, det_mul, det_transpose,
      det_of_isLowerTriangular _ (isLowerTriangular_toMatrix hLrows),
      det_of_isLowerTriangular _ (isLowerTriangular_toMatrix hVrows),
      ← diagProd_eq hLlen hLrows, ← diagProd_eq hVlen hVrows]
  calc
    (toMatrix n aRows).det = (-1) ^ swaps.length * (toMatrix n (applySwaps swaps aRows)).det := by
      rw [det_toMatrix_applySwaps hAlen hswaps, ← mul_assoc, ← mul_pow]
      simp
    _ = (-1) ^ swaps.length * (diagProd lRows * diagProd vRows) := by rw [hdetLU]

end Determinant

section Certificate

variable {K : Type*} [Field K] [CharZero K] {n : ℕ}

/-- Verify an LU certificate in which `aRows` represents `M`, and `lRows` and `vRows`
represent the two staircase factors. -/
public theorem det_eq_of_lu (M : Matrix (Fin n) (Fin n) K)
    (aRows lRows vRows : List (List ℚ)) (swaps : List (ℕ × ℕ)) (dq : ℚ) (d : K)
    (hA : (ofFn fun i ↦ ofFn fun j ↦ M i j) = aRows.map (List.map Rat.cast))
    (hcert : checkCertificate n aRows lRows vRows swaps dq)
    (hdK : d = (dq : K)) :
    M.det = d := by
  simp only [checkCertificate, Bool.and_eq_true] at hcert
  obtain ⟨hswaps, hsL, hsV, hmul, hd⟩ := hcert
  have hsgn : (-1) ^ swaps.length * (diagProd lRows * diagProd vRows) = dq := by
    rcases Nat.even_or_odd swaps.length with h | h <;> simp_all
  have hAlen : aRows.length = n := by simpa using (congrArg List.length hA).symm
  have hMA : M = (Rat.castHom K).mapMatrix (toMatrix n aRows) := by
    rw [RingHom.mapMatrix_apply, Rat.coe_castHom, ← toMatrix_map Rat.cast_zero, ← hA, toMatrix_ofFn]
  rwa [hMA, ← RingHom.map_det, det_toMatrix_eq hAlen hswaps hsL hsV hmul, hsgn, eq_comm]

end Certificate

end LUDet
