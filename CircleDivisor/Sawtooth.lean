import Mathlib

/-! The exact discontinuity convention and the shifted modulo-four formulas in Section 7. -/

namespace CircleDivisor.Sawtooth
noncomputable section

def psi (x : ℝ) : ℝ := x - (⌊x⌋ : ℤ) - 1 / 2

theorem psi_eq_fract (x : ℝ) : psi x = Int.fract x - 1 / 2 := rfl

theorem psi_bounds (x : ℝ) : -(1 / 2) ≤ psi x ∧ psi x < 1 / 2 := by
  have h₀ := Int.fract_nonneg x
  have h₁ := Int.fract_lt_one x
  rw [psi_eq_fract]
  constructor <;> linarith

theorem abs_psi_le (x : ℝ) : |psi x| ≤ 1 / 2 := by
  rw [abs_le]
  exact ⟨(psi_bounds x).1, (psi_bounds x).2.le⟩

theorem psi_at_integer (n : ℤ) : psi (n : ℝ) = -(1 / 2) := by simp [psi]

theorem psi_add_integer (x : ℝ) (n : ℤ) : psi (x + n) = psi x := by
  simp [psi, Int.floor_add_intCast]

theorem floor_eq (x : ℝ) : (⌊x⌋ : ℝ) = x - psi x - 1 / 2 := by
  unfold psi
  ring

/-- Modulo-four character on nonnegative integers, with the zero value at zero. -/
def chi4 (n : ℕ) : ℤ := if n % 4 = 1 then 1 else if n % 4 = 3 then -1 else 0

def partialSum (n : ℕ) : ℤ := ∑ d ∈ Finset.range (n + 1), chi4 d

theorem chi4_periodic (n : ℕ) : chi4 (n + 4) = chi4 n := by simp [chi4]

theorem chi4_abs_le (n : ℕ) : |chi4 n| ≤ 1 := by
  unfold chi4
  split_ifs <;> norm_num

theorem partialSum_formula (n : ℕ) :
    partialSum n = (↑((n + 3) / 4) : ℤ) - ↑((n + 1) / 4) := by
  induction n with
  | zero => norm_num [partialSum, chi4]
  | succ n ih =>
    have hrec : partialSum (n + 1) = partialSum n + chi4 (n + 1) := by
      unfold partialSum
      exact Finset.sum_range_succ _ _
    rw [hrec, ih]
    unfold chi4
    split_ifs <;> omega

theorem partialSum_zero_or_one (n : ℕ) : partialSum n = 0 ∨ partialSum n = 1 := by
  rw [partialSum_formula]
  omega

theorem partialSum_periodic (n : ℕ) : partialSum (n + 4) = partialSum n := by
  rw [partialSum_formula, partialSum_formula]
  omega

def floorDifference (u : ℝ) : ℝ :=
  (⌊(u + 3) / 4⌋ : ℤ) - (⌊(u + 1) / 4⌋ : ℤ)

/-- Equation (7.7), including all discontinuity endpoints. -/
theorem floorDifference_sawtooth (u : ℝ) :
    floorDifference u = 1 / 2 + psi (u / 4 + 1 / 4) - psi (u / 4 + 3 / 4) := by
  unfold floorDifference psi
  have h₁ : (u + 1) / 4 = u / 4 + 1 / 4 := by ring
  have h₃ : (u + 3) / 4 = u / 4 + 3 / 4 := by ring
  rw [h₁, h₃]
  ring

theorem floorDifference_periodic (u : ℝ) : floorDifference (u + 4) = floorDifference u := by
  have h₁ : (u + 4 + 1) / 4 = (u + 1) / 4 + 1 := by ring
  have h₃ : (u + 4 + 3) / 4 = (u + 3) / 4 + 1 := by ring
  simp [floorDifference, h₁, h₃, Int.floor_add_one]

/-- The constant offset in the last two circle sums is placed inside the phase. -/
theorem shifted_reciprocal_phase (X M t β : ℝ) (hM : M ≠ 0) (hX : X ≠ 0) :
    (X / M) * (1 / (4 * t) + M * β / X) = X / (4 * (M * t)) + β := by
  field_simp

theorem progression_reciprocal_phase (X M t a : ℝ) (hM : M ≠ 0) :
    (X / M) * ((1 / 4) * (t + a / (4 * M))⁻¹) = X / (4 * M * t + a) := by
  have hden : t + a / (4 * M) = (4 * M * t + a) / (4 * M) := by
    field_simp
  rw [hden, inv_div]
  field_simp

/-- The prospective linear error in (7.9) is exactly proportional to `X-U²`. -/
theorem circle_linear_cancellation (X U A : ℝ) (hU : U ≠ 0) :
    -(X / U) * (1 / 2 - A) + U * (1 / 2 - A) =
      -(X - U ^ 2) / U * (1 / 2 - A) := by
  field_simp
  ring

theorem floor_sqrt_remainder {X U : ℝ} (hU : 1 ≤ U)
    (hlo : U ^ 2 ≤ X) (hhi : X < (U + 1) ^ 2) :
    0 ≤ (X - U ^ 2) / U ∧ (X - U ^ 2) / U < 3 := by
  have hUpos : 0 < U := by linarith
  constructor
  · positivity
  · rw [div_lt_iff₀ hUpos]
    nlinarith

theorem circle_linear_cancellation_bound {X U A : ℝ} (hU : 1 ≤ U)
    (hlo : U ^ 2 ≤ X) (hhi : X < (U + 1) ^ 2) (hA : 0 ≤ A) (hA' : A ≤ 1) :
    |-(X / U) * (1 / 2 - A) + U * (1 / 2 - A)| ≤ 3 / 2 := by
  rw [circle_linear_cancellation X U A (by linarith), neg_div, neg_mul, abs_neg, abs_mul]
  have hr := floor_sqrt_remainder hU hlo hhi
  rw [abs_of_nonneg hr.1]
  have hAA : |1 / 2 - A| ≤ 1 / 2 := by rw [abs_le]; constructor <;> linarith
  have hh := mul_le_mul hr.2.le hAA (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 3)
  norm_num at hh
  exact hh

end
end CircleDivisor.Sawtooth
