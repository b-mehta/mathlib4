/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl, Sander Dahmen, Kim Morrison
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.RingTheory.Finiteness.Prod

/-!
# Results relating rank and torsion.

-/

public section

/-- A torsion module has rank zero. -/
theorem Module.IsTorsion.rank_eq_zero {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [Nontrivial R] (h : IsTorsion R M) : Module.rank R M = 0 := by
  by_contra! h'
  obtain ⟨f, hf⟩ := by rwa [← Cardinal.one_le_iff_ne_zero, one_le_rank_iff] at h'
  simpa [← map_smul, zero_notMem_nonZeroDivisors, hf] using @h (f 1)

theorem Module.IsTorsion.finrank_eq_zero {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [Nontrivial R] (h : IsTorsion R M) : finrank R M = 0 :=
  finrank_eq_zero_of_rank_eq_zero h.rank_eq_zero

variable {R M : Type*} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]

lemma Module.rank_eq_zero_iff_isTorsion : Module.rank R M = 0 ↔ Module.IsTorsion R M := by
  simp [IsTorsion, rank_eq_zero_iff]

@[deprecated (since := "2026-07-14")] alias
rank_eq_zero_iff_isTorsion := Module.rank_eq_zero_iff_isTorsion

/-- The `StrongRankCondition` is automatic. See `commRing_strongRankCondition`. -/
theorem Module.finrank_eq_zero_iff_isTorsion [StrongRankCondition R] [Module.Finite R M] :
    finrank R M = 0 ↔ Module.IsTorsion R M := by
  simp [← rank_eq_zero_iff_isTorsion (R := R), ← finrank_eq_rank]

/-- A finite `ℤ`-module has free rank zero. -/
lemma Module.finrank_int_zero_of_finite {D : Type*} [AddCommGroup D] [Finite D] :
    Module.finrank ℤ D = 0 :=
  Module.finrank_eq_zero_iff_isTorsion.mpr
    (isAddTorsion_iff_isTorsion_int.mp isAddTorsion_of_finite)

/-- The free rank of `F × D` equals that of `F` when `D` is finite. -/
lemma Module.finrank_prod_finite {F : Type*} [AddCommGroup F] [Module.Finite ℤ F]
    {D : Type*} [AddCommGroup D] [Finite D] :
    Module.finrank ℤ (F × D) = Module.finrank ℤ F := by
  have hkerD : Module.finrank ℤ (LinearMap.ker (LinearMap.fst ℤ F D)) = 0 := by
    rw [LinearMap.ker_fst, ← (LinearEquiv.ofInjective (LinearMap.inr ℤ F D)
      LinearMap.inr_injective).finrank_eq, Module.finrank_int_zero_of_finite]
  have key := Submodule.finrank_quotient_add_finrank (LinearMap.ker (LinearMap.fst ℤ F D))
  rw [hkerD, add_zero,
    (LinearMap.quotKerEquivOfSurjective _ LinearMap.fst_surjective).finrank_eq] at key
  exact key.symm
