import Mathlib

/-! Weighted finite hyperbola decomposition, the combinatorial step of Section 7. -/

namespace CircleDivisor.Hyperbola

theorem small_coordinate {a b N U : ℕ} (hN : N < (U + 1) ^ 2) (hab : a * b ≤ N) :
    a ≤ U ∨ b ≤ U := by
  by_contra! hn
  have hab' : (U + 1) * (U + 1) ≤ a * b :=
    Nat.mul_le_mul (by omega) (by omega)
  nlinarith

theorem square_inside {a b N U : ℕ} (hU : U ^ 2 ≤ N)
    (ha : a ≤ U) (hb : b ≤ U) : a * b ≤ N := by
  have hh := Nat.mul_le_mul ha hb
  nlinarith

/-- The exact inclusion-exclusion identity for every summand. -/
theorem indicator_decomposition {R : Type*} [AddCommGroup R]
    (a b N U : ℕ) (w : R) (hlo : U ^ 2 ≤ N) (hhi : N < (U + 1) ^ 2) :
    (if a * b ≤ N then w else 0) =
      (if a ≤ U ∧ a * b ≤ N then w else 0) +
      (if b ≤ U ∧ a * b ≤ N then w else 0) -
      (if a ≤ U ∧ b ≤ U then w else 0) := by
  have hsmall := small_coordinate (a := a) (b := b) hhi
  have hbox := square_inside (a := a) (b := b) hlo
  by_cases ha : a ≤ U <;> by_cases hb : b ≤ U <;> by_cases hab : a * b ≤ N <;>
    simp_all only [and_self, and_true, true_and, if_true, add_sub_cancel_right, not_le]
    <;> split_ifs <;> first | omega | simp_all

/-- Valid with arbitrary weights and arbitrary finite ambient integer intervals. -/
theorem weighted_hyperbola {R : Type*} [AddCommGroup R]
    (I J : Finset ℕ) (w : ℕ → ℕ → R) (N U : ℕ)
    (hlo : U ^ 2 ≤ N) (hhi : N < (U + 1) ^ 2) :
    (∑ a ∈ I, ∑ b ∈ J, if a * b ≤ N then w a b else 0) =
      (∑ a ∈ I, ∑ b ∈ J, if a ≤ U ∧ a * b ≤ N then w a b else 0) +
      (∑ a ∈ I, ∑ b ∈ J, if b ≤ U ∧ a * b ≤ N then w a b else 0) -
      (∑ a ∈ I, ∑ b ∈ J, if a ≤ U ∧ b ≤ U then w a b else 0) := by
  simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  exact indicator_decomposition a b N U (w a b) hlo hhi

/-- On the square ambient set, transposition exchanges the two hyperbola branches. -/
theorem symmetric_hyperbola (I : Finset ℕ) (w : ℕ → ℕ → ℝ) (N U : ℕ)
    (hw : ∀ a b, w a b = w b a) (hlo : U ^ 2 ≤ N) (hhi : N < (U + 1) ^ 2) :
    (∑ a ∈ I, ∑ b ∈ I, if a * b ≤ N then w a b else 0) =
      2 * (∑ a ∈ I, ∑ b ∈ I, if a ≤ U ∧ a * b ≤ N then w a b else 0) -
      (∑ a ∈ I, ∑ b ∈ I, if a ≤ U ∧ b ≤ U then w a b else 0) := by
  rw [weighted_hyperbola I I w N U hlo hhi]
  have hswap : (∑ a ∈ I, ∑ b ∈ I, if b ≤ U ∧ a * b ≤ N then w a b else 0) =
      ∑ a ∈ I, ∑ b ∈ I, if a ≤ U ∧ a * b ≤ N then w a b else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b hb
    apply Finset.sum_congr rfl
    intro a ha
    rw [hw a b, Nat.mul_comm a b]
  rw [hswap]
  ring

end CircleDivisor.Hyperbola
