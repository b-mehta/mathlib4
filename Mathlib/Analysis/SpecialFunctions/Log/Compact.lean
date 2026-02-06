/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Analysis.Normed.Module.RieszLemma
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Normed.Operator.Compact
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Spectral theory of compact operators

This file develops the spectral theory of compact operators on Banach spaces.
The main result is the Fredholm alternative for compact operators.

## Main results

* `antilipschitz_of_not_hasEigenvalue`: if `T` is a compact operator and `μ ≠ 0` is not an
  eigenvalue, then `T - μI` is antilipschitz.
* `fredholm_alternative`: the Fredholm alternative for compact operators.
-/

-- let X be a Banach space
variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
-- and T be a compact operator on it
variable {T : X →L[𝕜] X}

open Module End

/-- If a continuous linear map `f` satisfies `‖x‖ = 1 → 1 ≤ K * ‖f x‖`, then `f` is
antilipschitz with constant `K`. -/
lemma ContinuousLinearMap.antilipschitz_of_bound_of_norm_one {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (f : X →L[𝕜] Y) {K : NNReal} (h : ∀ x, ‖x‖ = 1 → 1 ≤ K * ‖f x‖) :
    AntilipschitzWith K f :=
  ContinuousLinearMap.antilipschitz_of_bound _ fun x ↦ by
    obtain rfl | hx := eq_or_ne x 0
    · simp
    simpa [norm_smul, field] using h ((‖x‖⁻¹ : 𝕜) • x) (norm_smul_inv_norm hx)

open Filter Topology in
/-- If `T : X →L[𝕜] X` is a compact operator on a Banach space `X`, and `μ ≠ 0` is not an
eigenvalue of `T`, then `T - μ • 1` is antilipschitz.

This is a useful step in the proof of the Fredholm alternative. -/
theorem antilipschitz_of_not_hasEigenvalue (hT : IsCompactOperator T)
    {μ : 𝕜} (hμ : μ ≠ 0) (h : ¬ HasEigenvalue (T : End 𝕜 X) μ) :
    ∃ K > 0, AntilipschitzWith K (T - μ • 1 : X →L[𝕜] X) := by
  suffices ∃ c > 0, ∀ x, ‖x‖ = 1 → c ≤ ‖(T - μ • 1) x‖ by
    obtain ⟨c, hc', hc⟩ := this
    refine ⟨c.toNNReal⁻¹, by positivity, ?_⟩
    apply ContinuousLinearMap.antilipschitz_of_bound_of_norm_one
    simpa [NNReal.coe_inv, le_inv_mul_iff₀', hc'] using hc
  -- Suppose not, then we can find a sequence of unit vectors xₙ such that (T - μ • 1) xₙ → 0.
  by_contra!
  obtain ⟨φ, hφ_anti, hφ_pos, hφ⟩ := exists_seq_strictAnti_tendsto (0 : ℝ)
  have (n : ℕ) : ∃ x, ‖x‖ = 1 ∧ ‖(T - μ • 1) x‖ < φ n := this (φ n) (hφ_pos n)
  choose x hx_norm hx_bound using this
  have hx_lim : Tendsto (fun n ↦ (T - μ • 1) (x n)) atTop (𝓝 0) := squeeze_zero_norm (by grind) hφ
  -- Define the sequence of vectors yₙ := T xₙ
  let y_ (n : ℕ) : X := T (x n)
  -- which are bounded away from zero.
  have hy_lower : ∀ᶠ n in atTop, ‖μ‖ / 2 ≤ ‖y_ n‖ := by
    filter_upwards [hφ.eventually_le_const (show ‖μ‖ / 2 > 0 by positivity)] with n hn
    have h₁ : ‖T (x n) - μ • x n‖ < φ n := by simpa using hx_bound n
    have h₂ : ‖μ‖ ≤ ‖T (x n)‖ + ‖T (x n) - μ • x n‖ := by
      simpa [norm_smul, hx_norm] using norm_le_norm_add_norm_sub (T (x n)) (μ • x n)
    grind
  -- The sequence yₙ is contained in the image of the closed unit ball under T, which is compact,
  -- since T is, so we can extract a convergent subsequence, and say y_ (ψ n) → y.
  obtain ⟨K, hK, hK'⟩ := hT.image_closedBall_subset_compact 1
  obtain ⟨y, hyK, ψ, hψ, hψy⟩ := hK.tendsto_subseq (x := y_) (fun n ↦ hK' ⟨x n, by simp [*], rfl⟩)
  -- However (T - μ • 1) yₙ = T ((T - μ • 1) xₙ) → 0
  have hy_lim : Tendsto (fun n ↦ (T - μ • 1) (y_ n)) atTop (nhds 0) := by
    have : Tendsto (fun n ↦ _) _ _ := T.continuous.continuousAt.tendsto.comp hx_lim
    simpa using this
  -- so (T - μ • 1) y = 0.
  have hy_eigen' : (T - μ • 1) y = 0 := by
    apply tendsto_nhds_unique _ (hy_lim.comp hψ.tendsto_atTop)
    have : Continuous (T - μ • 1 : X →L[𝕜] X) := by fun_prop
    exact this.continuousAt.tendsto.comp hψy
  -- Since yₙ are bounded away from 0, we must have y ≠ 0.
  have hy_ne : y ≠ 0 := by
    rintro rfl
    suffices ∀ᶠ n : ℕ in atTop, False by rwa [eventually_const] at this
    rw [NormedAddCommGroup.tendsto_nhds_zero] at hψy
    specialize hψy (‖μ‖ / 2) (by positivity)
    filter_upwards [hψ.tendsto_atTop.eventually hy_lower, hψy] using by grind
  -- So y is an eigenvector of T with eigenvalue μ,
  have : HasEigenvector (T : End 𝕜 X) μ y := by
    simpa [hasEigenvector_iff, mem_genEigenspace_one, hy_ne, sub_eq_zero] using hy_eigen'
  -- which is a contradiction.
  exact h (hasEigenvalue_of_hasEigenvector this)

/-- A variation of Riesz's lemma where we get a vector `x₀` of norm exactly 1. -/
theorem riesz_lemma_one
    {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {F : Subspace 𝕜 E} (hFc : IsClosed (F : Set E)) (hF : ∃ (x : E), x ∉ F) {r : ℝ} (hr : r < 1) :
    ∃ x₀ ∉ F, ‖x₀‖ = 1 ∧ ∀ y ∈ F, r ≤ ‖x₀ - y‖ := by
  obtain ⟨x₀, hx₀, h⟩ := riesz_lemma hFc hF hr
  have hx₀' : x₀ ≠ 0 := by rintro rfl; simp at hx₀
  refine ⟨(‖x₀‖⁻¹ : 𝕜) • x₀, ?_, norm_smul_inv_norm hx₀', ?_⟩
  · rwa [Submodule.smul_mem_iff]
    simpa
  intro y hy
  have h₂ : ‖(‖x₀‖ : 𝕜)⁻¹ • (x₀ - (‖x₀‖ : 𝕜) • y)‖ = ‖x₀‖⁻¹ * ‖x₀ - (‖x₀‖ : 𝕜) • y‖ := by
    rw [norm_smul, norm_inv, norm_algebraMap', norm_norm]
  have h₁ := h ((‖x₀‖ : 𝕜) • y) (F.smul_mem _ hy)
  rwa [← le_inv_mul_iff₀' (by simpa), ← h₂, smul_sub, inv_smul_smul₀] at h₁
  simpa using hx₀'

-- theorem riesz_lemma_of_norm_lt {c : 𝕜} (hc : 1 < ‖c‖) {R : ℝ} (hR : ‖c‖ < R) {F : Subspace 𝕜 E}
--     (hFc : IsClosed (F : Set E)) (hF : ∃ x : E, x ∉ F) :
--     ∃ x₀ : E, ‖x₀‖ ≤ R ∧ ∀ y ∈ F, 1 ≤ ‖x₀ - y‖ := by

theorem thing {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    {S : X →L[𝕜] X}
    (hS_not_surj : ¬ (S : X → X).Surjective)
    (hS_inj : (S : X → X).Injective)
    (hT_anti : Topology.IsClosedEmbedding S) :
    ∃ f : ℕ → X, (∀ n, ‖f n‖ = 1) ∧ Pairwise (2⁻¹ ≤ ‖f · - f ·‖) := by
  obtain ⟨x, hx⟩ : ∃ x : X, ∀ y, S y ≠ x := by simpa [Function.Surjective] using hS_not_surj
  let V (n : ℕ) : Submodule 𝕜 X := S.iterateRange n
  have hV_succ (n : ℕ) : V (n + 1) = (V n).map (S : End 𝕜 X) := LinearMap.iterateRange_succ
  have hV_closed (n : ℕ) : IsClosed (V n : Set X) := by
    induction n with
    | zero => simp [V, Module.End.one_eq_id]
    | succ n ih =>
      rw [hV_succ]
      apply hT_anti.isClosedMap _ ih
  have x (n : ℕ) : ∃ x ∈ V n, ‖x‖ = 1 ∧ ∀ y ∈ V (n + 1), 2⁻¹ ≤ ‖x - y‖ := by
    have h₁ : IsClosed (Submodule.comap (V n).subtype (V (n + 1)) : Set (V n)) := by
      simpa using (hV_closed (n + 1)).preimage_val
    have h₂ : ∃ x : V n, x ∉ (V (n + 1)).comap (V n).subtype := by
      suffices ∃ a, ∀ y, S y ≠ a by simpa [iterate_succ, V, (iterate_injective hS_inj n).eq_iff]
      use x
    obtain ⟨⟨x, hx⟩, hx', hxn, hxy⟩ := riesz_lemma_one h₁ h₂ (show 2⁻¹ < 1 by norm_num)
    simp only [Submodule.mem_comap, Submodule.subtype_apply, AddSubgroupClass.coe_norm,
      AddSubgroupClass.coe_sub, Subtype.forall] at hx' hxn hxy
    exact ⟨x, hx, hxn, fun y hy ↦ hxy y (S.iterateRange.monotone (by simp) hy) hy⟩
  choose x hxv hxn hxy using x
  refine ⟨x, hxn, ?_⟩
  intro m n hmn
  wlog! hmn' : m < n generalizing m n
  · rw [norm_sub_rev]
    exact this hmn.symm (by order)
  exact hxy m (x n) (S.iterateRange.monotone hmn' (hxv n))

/-- The Fredholm alternative for compact operators: if `T` is a compact operator and `μ ≠ 0`,
then either `μ` is an eigenvalue of `T`, or `μ` is in the resolvent set of `T`. -/
theorem fredholm_alternative [CompleteSpace X] (hT : IsCompactOperator T)
    {μ : 𝕜} (hμ : μ ≠ 0) :
    HasEigenvalue (T : End 𝕜 X) μ ∨ μ ∈ resolventSet 𝕜 T := by
  by_contra!
  obtain ⟨h₁, h₂⟩ := this
  let (eq := hS) S := (T - μ • 1)
  replace h₂ : ¬ (S : X → X).Bijective := by
    rw [spectrum.mem_resolventSet_iff, ← IsUnit.neg_iff,
      ContinuousLinearMap.isUnit_iff_bijective] at h₂
    convert h₂
    ext x
    simp [S]
  obtain ⟨K, -, hK : AntilipschitzWith K S⟩ := antilipschitz_of_not_hasEigenvalue hT hμ h₁
  obtain ⟨f, hf_norm, hf_pair⟩ := thing (mt (.intro hK.injective) h₂) hK.injective
    (hK.isClosedEmbedding S.uniformContinuous)
  have : Pairwise fun x₁ x₂ ↦ 2⁻¹ * K ≤ ‖T (f x₁) - T (f x₂)‖ := by
    intro m n hmn
    have := hK.le_mul_dist (f m) (f n)
    simp [dist_eq_norm_sub] at this
    sorry
  sorry


  -- have S_inj : (S : X → X).Injective := by
  --   rw [hasEigenvalue_iff, eigenspace_def, not_not, LinearMap.ker_eq_bot] at h₁
  --   exact h₁
  -- let V (n : ℕ) : Submodule ℂ X := (S ^ n).range

  -- sorry

-- #min_imports
