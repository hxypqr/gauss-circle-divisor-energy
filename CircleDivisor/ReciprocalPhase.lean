import CircleDivisor.ExternalInterfaces

/-!
# Actual reciprocal phases satisfy the Li--Yang phase interface

All derivatives are calculated from mathlib differentiation theorems. Closed-interval
endpoint derivatives are related to ambient derivatives by unique differentiability.
-/

namespace CircleDivisor.ReciprocalPhase
noncomputable section
open ExternalInterfaces

def phase (a s b : ℝ) (x : ℝ) : ℝ := b + a * (1 / (x + s))

theorem phase_contDiffAt (a s b x : ℝ) (n : ℕ) (hx : x + s ≠ 0) :
    ContDiffAt ℝ n (phase a s b) x := by
  exact contDiffAt_const.add (contDiffAt_const.mul
    (contDiffAt_const.div (contDiffAt_id.add contDiffAt_const) hx))

theorem one_div_iterated (j : ℕ) (x : ℝ) :
    iteratedDeriv j (fun y : ℝ => 1 / y) x =
      (-1) ^ j * (j.factorial : ℝ) * x ^ (-1 - (j : ℤ)) := by
  simpa only [iteratedDerivWithin_univ] using
    iteratedDerivWithin_one_div j isOpen_univ (Set.mem_univ x)

theorem phaseDerivative_formula (a s b : ℝ) (j : ℕ) (hj : 1 ≤ j)
    (x : ℝ) (hx : x ∈ Set.Icc (1 : ℝ) 2) (hne : x + s ≠ 0) :
    phaseDerivative j (phase a s b) x =
      a * ((-1) ^ j * (j.factorial : ℝ) * (x + s) ^ (-1 - (j : ℤ))) := by
  unfold phaseDerivative
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by norm_num : (1 : ℝ) < 2))
    (phase_contDiffAt a s b x j hne) hx]
  unfold phase
  rw [iteratedDeriv_const_add (by omega) b, iteratedDeriv_const_mul_field,
    iteratedDeriv_comp_add_const]
  dsimp only
  rw [one_div_iterated]

theorem phaseDerivative_one (a s b x : ℝ) (hx : x ∈ Set.Icc (1 : ℝ) 2)
    (hne : x + s ≠ 0) : phaseDerivative 1 (phase a s b) x = -a / (x + s) ^ 2 := by
  rw [phaseDerivative_formula a s b 1 (by omega) x hx hne]
  norm_num
  field_simp

theorem phaseDerivative_two (a s b x : ℝ) (hx : x ∈ Set.Icc (1 : ℝ) 2)
    (hne : x + s ≠ 0) : phaseDerivative 2 (phase a s b) x = 2 * a / (x + s) ^ 3 := by
  rw [phaseDerivative_formula a s b 2 (by omega) x hx hne]
  norm_num
  field_simp

theorem phaseDerivative_three (a s b x : ℝ) (hx : x ∈ Set.Icc (1 : ℝ) 2)
    (hne : x + s ≠ 0) : phaseDerivative 3 (phase a s b) x = -6 * a / (x + s) ^ 4 := by
  rw [phaseDerivative_formula a s b 3 (by omega) x hx hne]
  norm_num
  field_simp

theorem phase_curvature_formula (a s b x : ℝ) (hx : x ∈ Set.Icc (1 : ℝ) 2)
    (hne : x + s ≠ 0) :
    phaseDerivative 1 (phase a s b) x * phaseDerivative 3 (phase a s b) x -
      3 * (phaseDerivative 2 (phase a s b) x) ^ 2 = -6 * a ^ 2 / (x + s) ^ 6 := by
  rw [phaseDerivative_one a s b x hx hne, phaseDerivative_two a s b x hx hne,
    phaseDerivative_three a s b x hx hne]
  field_simp
  ring

theorem phase_contDiffOn (a s b : ℝ) (hs : 0 ≤ s) :
    ContDiffOn ℝ 3 (phase a s b) (Set.Icc 1 2) := by
  intro x hx
  exact (phase_contDiffAt a s b x 3 (by linarith [hx.1])).contDiffWithinAt

theorem phase_magnitude_bounds {a t : ℝ} (ha : 1 / 4 ≤ |a|) (ha' : |a| ≤ 1)
    (ht : 1 ≤ t) (ht' : t ≤ 3) :
    (1 / 10000 ≤ |-a / t ^ 2| ∧ |-a / t ^ 2| ≤ 10000) ∧
    (1 / 10000 ≤ |2 * a / t ^ 3| ∧ |2 * a / t ^ 3| ≤ 10000) ∧
    (1 / 10000 ≤ |-6 * a / t ^ 4| ∧ |-6 * a / t ^ 4| ≤ 10000) ∧
    1 / 10000 ≤ |-6 * a ^ 2 / t ^ 6| := by
  have ht0 : 0 < t := by linarith
  have h2 : 1 ≤ t ^ 2 ∧ t ^ 2 ≤ (9 : ℝ) := by constructor <;> nlinarith
  have h3 : 1 ≤ t ^ 3 ∧ t ^ 3 ≤ (27 : ℝ) := by
    constructor
    · nlinarith [sq_nonneg (t - 1)]
    · have hh := mul_le_mul h2.2 ht' ht0.le (by norm_num : (0 : ℝ) ≤ 9)
      nlinarith
  have h4 : 1 ≤ t ^ 4 ∧ t ^ 4 ≤ (81 : ℝ) := by
    constructor <;> nlinarith [sq_nonneg (t ^ 2 - 1), sq_nonneg (t ^ 2 - 9)]
  have h6 : 1 ≤ t ^ 6 ∧ t ^ 6 ≤ (729 : ℝ) := by
    constructor <;> nlinarith [sq_nonneg (t ^ 3 - 1), sq_nonneg (t ^ 3 - 27)]
  have ha2 : 1 / 16 ≤ a ^ 2 := by nlinarith [sq_abs a, sq_nonneg (|a| - 1 / 4)]
  simp only [abs_div, abs_neg, abs_mul, abs_of_pos (pow_pos ht0 _), abs_pow]
  norm_num
  rw [le_div_iff₀ (pow_pos ht0 2), div_le_iff₀ (pow_pos ht0 2),
    le_div_iff₀ (pow_pos ht0 3), div_le_iff₀ (pow_pos ht0 3),
    le_div_iff₀ (pow_pos ht0 4), div_le_iff₀ (pow_pos ht0 4),
    le_div_iff₀ (pow_pos ht0 6)]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩ <;> nlinarith [sq_abs a]

/-- Uniformly covers all reciprocal phases used in §7, including additive constants
of arbitrary size and the shifted progressions. -/
theorem reciprocal_phase_control (a s b : ℝ) (ha : 1 / 4 ≤ |a|) (ha' : |a| ≤ 1)
    (hs : 0 ≤ s) (hs' : s ≤ 1) : PhaseControl (1 / 10000) 10000 (phase a s b) := by
  refine ⟨phase_contDiffOn a s b hs, ?_, ?_⟩
  · intro j hj hj' x hx
    have ht : 1 ≤ x + s := by linarith [hx.1]
    have ht' : x + s ≤ 3 := by linarith [hx.2]
    have hne : x + s ≠ 0 := by linarith
    have hh := phase_magnitude_bounds ha ha' ht ht'
    interval_cases j
    · simpa only [phaseDerivative_one a s b x hx hne] using hh.1
    · simpa only [phaseDerivative_two a s b x hx hne] using hh.2.1
    · simpa only [phaseDerivative_three a s b x hx hne] using hh.2.2.1
  · intro x hx
    have ht : 1 ≤ x + s := by linarith [hx.1]
    have ht' : x + s ≤ 3 := by linarith [hx.2]
    have hne : x + s ≠ 0 := by linarith
    rw [phase_curvature_formula a s b x hx hne]
    exact (phase_magnitude_bounds ha ha' ht ht').2.2.2

theorem one_div_phase_control : PhaseControl (1 / 10000) 10000 (fun x : ℝ => 1 / x) := by
  have heq : phase 1 0 0 = fun x : ℝ => 1 / x := by ext x; simp [phase]
  rw [← heq]
  exact reciprocal_phase_control 1 0 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem affine_reciprocal_phase_control (a b : ℝ) (ha : 1 / 4 ≤ |a|) (ha' : |a| ≤ 1) :
    PhaseControl (1 / 10000) 10000 (fun x : ℝ => a / x + b) := by
  have heq : phase a 0 b = fun x : ℝ => a / x + b := by ext x; simp [phase]; ring
  rw [← heq]
  exact reciprocal_phase_control a 0 b ha ha' (by norm_num) (by norm_num)

theorem shifted_reciprocal_phase_control (a s b : ℝ)
    (ha : 1 / 4 ≤ |a|) (ha' : |a| ≤ 1) (hs : 0 ≤ s) (hs' : s ≤ 1) :
    PhaseControl (1 / 10000) 10000 (fun x : ℝ => a / (x + s) + b) := by
  have heq : phase a s b = fun x : ℝ => a / (x + s) + b := by ext x; unfold phase; ring
  rw [← heq]
  exact reciprocal_phase_control a s b ha ha' hs hs'

/-- The constant shifts of the last two circle sums are arbitrary real numbers;
they do not change any derivative or any interface constant. -/
theorem circle_shifted_phase_control (b : ℝ) :
    PhaseControl (1 / 10000) 10000 (fun x : ℝ => 1 / (4 * x) + b) := by
  have heq : (fun x : ℝ => (1 / 4 : ℝ) / x + b) = fun x : ℝ => 1 / (4 * x) + b := by
    ext x
    ring
  rw [← heq]
  exact affine_reciprocal_phase_control (1 / 4) b (by norm_num) (by norm_num)

/-- The residue-class phases used for d=4j+1 and d=4j+3 in §7.3. The constants
are independent of the dyadic scale M and of the residue a. -/
theorem circle_progression_phase_control (a M : ℝ) (ha : 1 ≤ a) (ha' : a ≤ 3)
    (hM : 1 ≤ M) :
    PhaseControl (1 / 10000) 10000
      (fun x : ℝ => (1 / 4) * (x + a / (4 * M))⁻¹) := by
  have hs : 0 ≤ a / (4 * M) := by positivity
  have hs' : a / (4 * M) ≤ 1 := by
    rw [div_le_iff₀ (by positivity : 0 < 4 * M)]
    linarith
  have heq : phase (1 / 4) (a / (4 * M)) 0 =
      fun x : ℝ => (1 / 4) * (x + a / (4 * M))⁻¹ := by
    ext x
    simp [phase, one_div]
  rw [← heq]
  exact reciprocal_phase_control (1 / 4) (a / (4 * M)) 0
    (by norm_num) (by norm_num) hs hs'

end
end CircleDivisor.ReciprocalPhase
