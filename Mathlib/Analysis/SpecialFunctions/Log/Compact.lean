import Mathlib

-- let X be a Banach space
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
-- and T be a compact operator on it
variable {T : X →L[ℂ] X} (hT : IsCompactOperator T)

open Module.End

open Filter Topology in
theorem far_away {μ : ℂ} (hμ : μ ≠ 0) (hT : IsCompactOperator T)
    (h : ¬ HasEigenvalue (T : X →ₗ[ℂ] X) μ) :
    ∃ c > 0, ∀ x, c * ‖x‖ ≤ ‖(T - μ • 1) x‖ := by
  -- By homogeneity, it suffices to establish the claim for unit vectors x.
  suffices ∃ c > 0, ∀ x, ‖x‖ = 1 → c ≤ ‖(T - μ • 1) x‖ by
    obtain ⟨c, hc', hc⟩ := this
    refine ⟨c, hc', fun x ↦ ?_⟩
    obtain h | h := eq_or_ne x 0
    · simp [h]
    simpa [norm_smul, le_inv_mul_iff₀', norm_pos_iff, h] using hc _ (norm_smul_inv_norm (𝕜 := ℂ) h)
  -- Suppose not, then we can find a sequence of unit vectors xₙ such that (T - μ • 1) xₙ → 0.
  by_contra!
  obtain ⟨φ, hφ_anti, hφ_pos, hφ⟩ := exists_seq_strictAnti_tendsto (0 : ℝ)
  have : ∀ n, ∃ x, ‖x‖ = 1 ∧ ‖(T - μ • 1) x‖ < φ n := by
    intro n
    exact this (φ n) (hφ_pos n)
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
  -- However (T - μ) yₙ = T (T - μ • 1) xₙ → 0
  have hy_lim : Tendsto (fun n ↦ (T - μ • 1) (y_ n)) atTop (nhds 0) := by
    have : Tendsto (fun n ↦ _) _ _ := T.continuous.continuousAt.tendsto.comp hx_lim
    simpa using this
  -- so (T - μ) y = 0.
  have hy_eigen' : (T - μ • 1) y = 0 := by
    apply tendsto_nhds_unique _ (hy_lim.comp hψ.tendsto_atTop)
    have : Continuous (T - μ • 1 : X →L[ℂ] X) := by fun_prop
    exact this.continuousAt.tendsto.comp hψy
  -- Since yₙ are bounded away from 0, we must have y ≠ 0.
  have hy_ne : y ≠ 0 := by
    rintro rfl
    suffices ∀ᶠ n : ℕ in atTop, False by rwa [eventually_const] at this
    rw [NormedAddCommGroup.tendsto_nhds_zero] at hψy
    specialize hψy (‖μ‖ / 2) (by positivity)
    filter_upwards [hψ.tendsto_atTop.eventually hy_lower, hψy] using by grind
  -- So y is an eigenvector of T with eigenvalue μ,
  have : HasEigenvector (T : X →ₗ[ℂ] X) μ y := by
    rw [hasEigenvector_iff]
    rw [mem_genEigenspace_one]
    simpa [hy_ne, sub_eq_zero] using hy_eigen'
  -- which is a contradiction.
  exact h (hasEigenvalue_of_hasEigenvector this)

theorem fredholm_alternative [CompleteSpace X] {μ : ℂ} (hμ : μ ≠ 0) :
    HasEigenvalue (T : X →ₗ[ℂ] X) μ ∨ μ ∈ resolventSet ℂ T := by
  by_contra!
  obtain ⟨h₁, h₂⟩ := this
  let S := (T - μ • 1)
  replace h₂ : ¬ (S : X → X).Bijective := by
    rw [spectrum.mem_resolventSet_iff, ← IsUnit.neg_iff,
      ContinuousLinearMap.isUnit_iff_bijective] at h₂
    convert h₂
    ext x
    simp [S]
  have : (S : X → X).Injective := by
    sorry
  sorry
