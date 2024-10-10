import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.GroupWithZero.Canonical

variable {𝔸 : Type*}

@[inline]
noncomputable def is₀₁ [Zero 𝔸] [One 𝔸] (a : 𝔸) := a = 0 ∨ a = 1

@[simp]
lemma is₀₁_zero [Zero 𝔸] [One 𝔸] : is₀₁ (0 : 𝔸) := by simp only [is₀₁, true_or]
@[simp]
lemma is₀₁_one [Zero 𝔸] [One 𝔸] : is₀₁ (1 : 𝔸) := by simp only [is₀₁, or_true]

@[simp]
theorem is₀₁_if_zero_or_one [Zero 𝔸] [One 𝔸] {b : Prop} [Decidable b] : is₀₁ (if b then (1 : 𝔸) else 0) := by
  by_cases h : b <;> simp [h]

theorem is₀₁_le_one [LinearOrderedCommMonoidWithZero 𝔸] [ZeroLEOneClass 𝔸] {x : 𝔸} (h : is₀₁ x) : x ≤ 1 := by
  unfold is₀₁ at h
  cases h with
  | inl h => rw [h] ; exact zero_le_one
  | inr h => rw [h]

theorem is₀₁_not_zero_then_one [Zero 𝔸] [One 𝔸] [NeZero (1 : 𝔸)] (x : 𝔸) (h : is₀₁ x) : (¬x = 0) = (x = 1) := by
  simp_all [is₀₁, false_or, ne_eq]
  cases h <;> rename_i h'
  · simp_all only [zero_ne_one, iff_false, not_true_eq_false, not_false_eq_true]
  · simp_all only [one_ne_zero, iff_true, not_false_eq_true]
