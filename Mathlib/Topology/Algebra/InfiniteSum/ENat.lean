/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.Data.Set.Card
public import Mathlib.Topology.Instances.ENat
public import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Infinite sums in extended natural numbers

This file proves results on infinite sums of constants in `ℕ∞`, relating them to cardinalities.
-/

open Filter Set

namespace ENat

theorem tsum_const {α : Type*} (c : ENat) : ∑' (_ : α), c = ENat.card α * c := by
  obtain rfl | hc := eq_or_ne c 0
  · simp
  obtain hfin | hinf := fintypeOrInfinite α
  · simp [tsum_fintype]
  · simp only [card_eq_top_of_infinite]
    apply HasSum.tsum_eq _
    change Filter.Tendsto _ _ _
    simp only [Finset.sum_const, nsmul_eq_mul, ne_eq, hc, not_false_eq_true, top_mul]
    rw [tendsto_nhds_top_iff_natCast_lt]
    intro n
    obtain ⟨s, hs⟩ := Infinite.exists_subset_card_eq α (n + 1)
    filter_upwards [Filter.eventually_ge_atTop s] intro t ht
    calc (n : ℕ∞) < s.card := by simp only [Nat.cast_lt, hs, Nat.lt_succ_self n]
      _ ≤ t.card := by simpa using Finset.card_le_card ht
      _ = t.card * 1 := by simp
      _ ≤ t.card * c := mul_le_mul_right (ENat.one_le_iff_ne_zero.2 hc)

theorem tsum_set_const {α : Type*} (s : Set α) (c : ENat) :
    ∑' (_ : s), c = s.encard * c := by
  rw [ENat.tsum_const, Set.encard]

@[simp]
theorem tsum_one {α : Type*} : ∑' (_ : α), (1 : ENat) = ENat.card α := by
  simp [ENat.tsum_const]

theorem tsum_set_one {α : Type*} (s : Set α) :
    ∑' (_ : s), (1 : ENat) = s.encard := by
  rw [ENat.tsum_one, Set.encard]

end ENat
