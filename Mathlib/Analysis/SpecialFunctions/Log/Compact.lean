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
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order


/-!
# Spectral theory of compact operators

This file develops the spectral theory of compact operators on Banach spaces.
The main result is the Fredholm alternative for compact operators.

## Main results

* `antilipschitz_of_not_hasEigenvalue`: if `T` is a compact operator and `μ ≠ 0` is not an
  eigenvalue, then `T - μI` is antilipschitz.
* `fredholm_alternative`: the Fredholm alternative for compact operators.

We follow https://terrytao.wordpress.com/2011/04/10/a-proof-of-the-fredholm-alternative/
-/

-- let X be a Banach space
variable {𝕜 X : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
-- and T be a compact operator on it
variable {T : X →L[𝕜] X}

open Module End

/-- If a continuous linear map `f` satisfies `‖x‖ = 1 → 1 ≤ K * ‖f x‖`, then `f` is
antilipschitz with constant `K`. -/
lemma ContinuousLinearMap.antilipschitz_of_bound_of_norm_one {𝕜 : Type*} [RCLike 𝕜] {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (f : X →L[𝕜] Y) {K : NNReal} (h : ∀ x, ‖x‖ = 1 → 1 ≤ K * ‖f x‖) :
    AntilipschitzWith K f :=
  ContinuousLinearMap.antilipschitz_of_bound _ fun x ↦ by
    obtain rfl | hx := eq_or_ne x 0
    · simp
    simpa [norm_smul, field] using h ((‖x‖⁻¹ : 𝕜) • x) (norm_smul_inv_norm hx)

open Filter Topology in
/-- If `T : X →L[𝕜] X` is a compact operator on a Banach space `X`, and `μ ≠ 0` is not an
eigenvalue of `T`, then `T - μ • 1` is antilipschitz with positive constant.
That is, `T - μ • 1` is bounded below as an operator.

This is a useful step in the proof of the Fredholm alternative. for compact operators. -/
theorem antilipschitz_of_not_hasEigenvalue (hT : IsCompactOperator T)
    {μ : 𝕜} (hμ : μ ≠ 0) (h : ¬ HasEigenvalue (T : End 𝕜 X) μ) :
    ∃ K > 0, AntilipschitzWith K (T - μ • 1 : X →L[𝕜] X) := by
  -- Suppose not, then for every K > 0, there is some x such that ‖(T - μ • 1) x‖ < K * ‖x‖.
  by_contra! hK
  replace hK : ∀ K > 0, ∃ x, ‖(T - μ • 1) x‖ < K * ‖x‖ := by
    contrapose! hK
    obtain ⟨K, hK₀, hK⟩ := hK
    refine ⟨K.toNNReal⁻¹, by positivity, ?_⟩
    apply AddMonoidHomClass.antilipschitz_of_bound
    simpa [NNReal.coe_inv, le_inv_mul_iff₀, hK₀, hK₀.le] using hK
  -- In fact, there is a lower bound `c` such that for every ε > 0, there is an `x` with norm
  -- in the interval `[c, 1]` such that `‖(T - μ • 1) x‖ < ε`.
  -- (In the case of an RCLike field, where we can rescale, we could even get `‖x‖ = 1`, but we
  -- don't need that.)
  replace hK : ∃ c > 0, ∀ ε > 0, ∃ x, ‖x‖ ≤ 1 ∧ c ≤ ‖x‖ ∧ ‖(T - μ • 1) x‖ < ε := by
    obtain ⟨C, hC⟩ := NormedField.exists_one_lt_norm 𝕜
    refine ⟨‖C‖⁻¹, by positivity, fun ε hε ↦ ?_⟩
    obtain ⟨x, hx⟩ := hK ε (by positivity)
    have : x ≠ 0 := by aesop
    obtain ⟨η, hη, h₁, h₂, h₃⟩ := rescale_to_shell hC (ε := 1) (by simp) this
    refine ⟨η • x, h₁.le, by simpa using h₂, ?_⟩
    grw [map_smul, norm_smul, hx, mul_left_comm, ← norm_smul]
    linear_combination ε * h₁
  obtain ⟨c, hc₀, hc⟩ := hK
  obtain ⟨φ, hφ_anti, hφ_pos, hφ⟩ := exists_seq_strictAnti_tendsto (0 : ℝ)
  -- Then find a sequence of vectors `xₙ` with norm in the interval `[c, 1]` such
  -- that `‖(T - μ • 1) xₙ‖ < φ n`, where `φ n` is a sequence of positive numbers tending to zero.
  have (n : ℕ) : ∃ x, ‖x‖ ≤ 1 ∧ c ≤ ‖x‖ ∧ ‖(T - μ • 1) x‖ < φ n := hc (φ n) (hφ_pos n)
  choose x hx_norm_upper hx_norm_lower hx_bound using this
  have hx_lim : Tendsto (fun n ↦ (T - μ • 1) (x n)) atTop (𝓝 0) := squeeze_zero_norm (by grind) hφ
  -- Define the sequence of vectors yₙ := T xₙ
  let y_ (n : ℕ) : X := T (x n)
  -- which are bounded away from zero.
  have hy_lower : ∃ d > 0, ∀ᶠ n in atTop, d ≤ ‖y_ n‖ := by
    refine ⟨(‖μ‖ * c) / 2, by positivity, ?_⟩
    filter_upwards [hφ.eventually_le_const (show (‖μ‖ * c) / 2 > 0 by positivity)] with n hn
    have h₁ : ‖T (x n) - μ • x n‖ < φ n := by simpa using hx_bound n
    have h₂ : ‖μ‖ * ‖x n‖ ≤ ‖T (x n)‖ + ‖T (x n) - μ • x n‖ := by
      simpa [norm_smul] using norm_le_norm_add_norm_sub (T (x n)) (μ • x n)
    linear_combination h₂ + h₁ + hn + ‖μ‖ * hx_norm_lower n
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
    obtain ⟨d, hd₀, hd⟩ := hy_lower
    rintro rfl
    suffices ∀ᶠ n : ℕ in atTop, False by rwa [eventually_const] at this
    rw [NormedAddCommGroup.tendsto_nhds_zero] at hψy
    filter_upwards [hψ.tendsto_atTop.eventually hd, hψy d (by positivity)] using by grind
  -- So y is an eigenvector of T with eigenvalue μ,
  have : HasEigenvector (T : End 𝕜 X) μ y := by
    simpa [hasEigenvector_iff, mem_genEigenspace_one, hy_ne, sub_eq_zero] using hy_eigen'
  -- which is a contradiction.
  exact h (hasEigenvalue_of_hasEigenvector this)

/-- A variation of Riesz's lemma for where we get a vector `x₀` of norm exactly 1. -/
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

/--
Given an endomorphism `S` of a normed space that's a closed embedding but not surjective, we can
find a sequence of vectors `f n`, living inside a shell, such that `f n` is in the
range of `S ^ n` but is at least `1` away from any vector in the range of `S ^ (n + 1)`.
This is a useful construction for the proof of the Fredholm alternative for compact operators.
-/
theorem exists_seq {𝕜 X : Type*}
    [NontriviallyNormedField 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    {S : End 𝕜 X} (hS_not_surj : ¬ (S : X → X).Surjective)
    (hS_anti : Topology.IsClosedEmbedding S)
    {c : 𝕜} (hc : 1 < ‖c‖) {R : ℝ} (hR : ‖c‖ < R) :
    ∃ f : ℕ → X,
      (∀ n, 1 ≤ ‖f n‖) ∧ (∀ n, ‖f n‖ ≤ R) ∧ (∀ n, f n ∈ (S ^ n).range) ∧
      (∀ n, ∀ y ∈ (S ^ (n + 1)).range, 1 ≤ ‖f n - y‖) := by
  obtain ⟨x, hx⟩ : ∃ x : X, ∀ y, S y ≠ x := by simpa [Function.Surjective] using hS_not_surj
  let V (n : ℕ) : Submodule 𝕜 X := S.iterateRange n
  have hV_succ (n : ℕ) : V (n + 1) = (V n).map (S : End 𝕜 X) := LinearMap.iterateRange_succ
  have hV_closed (n : ℕ) : IsClosed (V n : Set X) := by
    induction n with
    | zero => simp [V, Module.End.one_eq_id]
    | succ n ih =>
      rw [hV_succ]
      apply hS_anti.isClosedMap _ ih
  have x (n : ℕ) : ∃ x ∈ V n, 1 ≤ ‖x‖ ∧ ‖x‖ ≤ R ∧ ∀ y ∈ V (n + 1), 1 ≤ ‖x - y‖ := by
    have h₁ : IsClosed (Submodule.comap (V n).subtype (V (n + 1)) : Set (V n)) := by
      simpa using (hV_closed (n + 1)).preimage_val
    have h₂ : ∃ x : V n, x ∉ (V (n + 1)).comap (V n).subtype := by
      simpa [iterate_succ, V, (iterate_injective hS_anti.injective n).eq_iff] using by use x
    obtain ⟨⟨x, hx⟩, hxn, hxy⟩ := riesz_lemma_of_norm_lt hc hR h₁ h₂
    simp only [Submodule.mem_comap, Submodule.subtype_apply, AddSubgroupClass.coe_norm,
      AddSubgroupClass.coe_sub, Subtype.forall] at hxn hxy
    exact ⟨x, hx, (by simpa using hxy 0), hxn,
      fun y hy ↦ hxy y (S.iterateRange.monotone (by simp) hy) hy⟩
  choose x hxv hxn hxn' hxy using x
  exact ⟨x, hxn, hxn', hxv, hxy⟩

/-- The Fredholm alternative for compact operators: if `T` is a compact operator and `μ ≠ 0`,
then either `μ` is an eigenvalue of `T`, or `μ` is in the resolvent set of `T`. -/
theorem fredholm_alternative {𝕜 X : Type*}
    [NontriviallyNormedField 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [CompleteSpace X] {T : X →L[𝕜] X} (hT : IsCompactOperator T)
    {μ : 𝕜} (hμ : μ ≠ 0) : HasEigenvalue (T : End 𝕜 X) μ ∨ μ ∈ resolventSet 𝕜 T := by
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
  obtain ⟨c, hc⟩ := NormedField.exists_one_lt_norm 𝕜
  obtain ⟨f, hf_norm_lower, hf_norm_upper, hf_mem, hf_far⟩ :=
    exists_seq (mt (.intro hK.injective) h₂)
    (hK.isClosedEmbedding S.uniformContinuous) (c := c) hc (R := ‖c‖ + 1) (by simp)
  have hf_mem' (n : ℕ) : S (f n) ∈ ((S : End 𝕜 X) ^ (n + 1)).range := by
    rw [iterate_succ']
    rw [LinearMap.range_comp]
    exact ⟨f n, hf_mem n, rfl⟩
  have hp : Pairwise fun x₁ x₂ ↦ ‖μ‖ ≤ ‖T (f x₁) - T (f x₂)‖ := by
    intro m n hmn
    wlog! hmn' : m < n generalizing m n
    · rw [norm_sub_rev]
      exact this hmn.symm (by order)
    let u : X := μ⁻¹ • (S (f n) - S (f m) + μ • f n)
    have hu : μ • (f m - u) = (T (f m) - T (f n)) := by
      rw [smul_sub, smul_inv_smul₀ hμ]
      simp [S]
      linear_combination (norm := module)
    have : u ∈ ((S : End 𝕜 X) ^ (m + 1)).range := by
      apply Submodule.smul_mem _ _ (Submodule.add_mem _ _ _)
      · exact Submodule.sub_mem _ ((S : End 𝕜 X).iterateRange.monotone (by lia) (hf_mem' _))
          (hf_mem' _)
      · exact Submodule.smul_mem _ μ ((S : End 𝕜 X).iterateRange.monotone (by lia) (hf_mem n))
    rw [← hu, norm_smul, mul_comm]
    grw [← hf_far _ u this, one_mul]
  obtain ⟨K, hK, hK'⟩ := hT.image_closedBall_subset_compact (‖c‖ + 1)
  obtain ⟨y, hyK, ψ, hψ, hψy⟩ := hK.tendsto_subseq (fun n ↦ hK' ⟨f n, by simp [*], rfl⟩)
  replace hψy := hψy.cauchySeq
  rw [Metric.cauchySeq_iff'] at hψy
  obtain ⟨N, hN⟩ := hψy ‖μ‖ (by positivity)
  simp only [dist_eq_norm_sub, ContinuousLinearMap.coe_coe, Function.comp_apply] at hN
  have := hN (N + 1) (by simp)
  refine this.not_ge ?_
  apply hp
  simp [hψ.injective.eq_iff]

theorem ContinuousLinearMap.isUnit_toLinearMap_iff [CompleteSpace X] {T : X →L[𝕜] X} :
    IsUnit T ↔ IsUnit (T : End 𝕜 X) := by
  rw [ContinuousLinearMap.isUnit_iff_bijective, Module.End.isUnit_iff]
  rfl

theorem ContinuousLinearMap.spectrum_eq [CompleteSpace X] :
    spectrum 𝕜 (T : X →L[𝕜] X) = spectrum 𝕜 (T : End 𝕜 X) := by
  ext μ
  rw [spectrum, resolventSet, Set.mem_compl_iff, Set.mem_setOf,
    ContinuousLinearMap.isUnit_toLinearMap_iff]
  rfl

theorem hasEigenvalue_iff_mem_spectrum [CompleteSpace X] (hT : IsCompactOperator T)
    {μ : 𝕜} (hμ : μ ≠ 0) :
    HasEigenvalue (T : End 𝕜 X) μ ↔ μ ∈ spectrum 𝕜 T := by
  constructor
  · intro hμ'
    rw [ContinuousLinearMap.spectrum_eq]
    exact hμ'.mem_spectrum
  · intro h
    exact (fredholm_alternative hT hμ).resolve_right h
