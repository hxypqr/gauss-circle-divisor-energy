import Mathlib

/-!
# Exact algebraic optimization (manuscript §6.4)

All statements in this file are unconditional real-algebra theorems.  In particular,
the exponent and the square identity are derived from `Real.sqrt`, rather than
introduced as external assumptions.
-/

namespace CircleDivisor.Optimization

noncomputable section

def theta : ℝ := (33333 - 8 * Real.sqrt 64515) / 99856

def hardInterval (x : ℝ) : Prop := 2 * theta - 1 < x ∧ x ≤ -theta

def kappa (x : ℝ) : ℝ := -(47 / 200 : ℝ) - 24 * x / 25

def lam (x : ℝ) : ℝ := (51 / 200 : ℝ) + 17 * x / 25

def transition : ℝ := -(149 / 464 : ℝ)

def qChoice (x : ℝ) : ℝ := if x ≤ transition then 4 + lam x / kappa x else 9 / 2

def E (x q : ℝ) : ℝ := (-(9 / 50 : ℝ) + 22 / (25 * q)) * x +
  49 / 200 + 33 / (100 * q)

def E1 (x : ℝ) : ℝ := (2208 * x ^ 2 + 9396 * x + 1963) / (40 * (632 * x + 137))

def E2 (x : ℝ) : ℝ := (28 * x + 573) / 1800

def x0 : ℝ := (25280 * theta - 9396) / 4416

theorem sqrt_64515_sq : (Real.sqrt (64515 : ℝ)) ^ 2 = 64515 :=
  Real.sq_sqrt (by norm_num)

theorem theta_lower : (3134615421 : ℝ) / 10000000000 < theta := by
  have hs := sqrt_64515_sq
  have hn := Real.sqrt_nonneg (64515 : ℝ)
  have hupper : Real.sqrt (64515 : ℝ) < (33333 -
      99856 * ((3134615421 : ℝ) / 10000000000)) / 8 := by
    nlinarith
  dsimp [theta]
  linarith

theorem theta_upper : theta < (3134615422 : ℝ) / 10000000000 := by
  have hs := sqrt_64515_sq
  have hn := Real.sqrt_nonneg (64515 : ℝ)
  have hlower : (33333 -
      99856 * ((3134615422 : ℝ) / 10000000000)) / 8 < Real.sqrt (64515 : ℝ) := by
    nlinarith
  dsimp [theta]
  linarith

theorem theta_bounds : (3134615421 : ℝ) / 10000000000 < theta ∧
    theta < (3134615422 : ℝ) / 10000000000 := ⟨theta_lower, theta_upper⟩

theorem theta_numerical_conditions :
    (49 : ℝ) / 164 < theta ∧ (4 : ℝ) / 13 < theta ∧
    (253 : ℝ) / 808 < theta ∧ (89 : ℝ) / 284 < theta ∧
    (573 : ℝ) / 1828 < theta ∧ (5 : ℝ) / 16 < theta := by
  have h := theta_lower
  constructor <;> try linarith
  constructor <;> try linarith
  constructor <;> try linarith
  constructor <;> try linarith
  constructor <;> linarith

theorem zero_discriminant :
    (9396 - 25280 * theta) ^ 2 - 8832 * (1963 - 5480 * theta) = 0 := by
  dsimp [theta]
  nlinarith [sqrt_64515_sq]

theorem x0_location : 2 * theta - 1 < x0 ∧ x0 < transition ∧ transition < -theta := by
  have hl := theta_lower
  have hu := theta_upper
  dsimp [x0, transition]
  constructor <;> try linarith
  constructor <;> linarith

theorem hard_interval_basic {x : ℝ} (hx : hardInterval x) :
    -(3 / 8 : ℝ) < x ∧ x < -(89 / 284 : ℝ) := by
  obtain ⟨hxl, hxu⟩ := hx
  have hl := theta_lower
  constructor <;> linarith

theorem kappa_pos {x : ℝ} (hx : hardInterval x) : 0 < kappa x := by
  have h := (hard_interval_basic hx).2
  dsimp [kappa]
  linarith

theorem lam_pos {x : ℝ} (hx : hardInterval x) : 0 < lam x := by
  have h := (hard_interval_basic hx).1
  dsimp [lam]
  linarith

theorem lam_le_kappa {x : ℝ} (hx : hardInterval x) : lam x ≤ kappa x := by
  have h := (hard_interval_basic hx).2
  dsimp [lam, kappa]
  linarith

theorem denominator_neg {x : ℝ} (hx : hardInterval x) : 632 * x + 137 < 0 := by
  have h := (hard_interval_basic hx).2
  linarith

theorem transition_identity : kappa transition = 2 * lam transition := by
  norm_num [kappa, lam, transition]

theorem first_region {x : ℝ} (hx : x ≤ transition) : 2 * lam x ≤ kappa x := by
  dsimp [transition, lam, kappa] at *
  linarith

theorem second_region {x : ℝ} (hx : transition ≤ x) : kappa x ≤ 2 * lam x := by
  dsimp [transition, lam, kappa] at *
  linarith

theorem lower_ratio {x : ℝ} (hx : hardInterval x) : 11 * lam x ≤ 7 * kappa x := by
  have h := (hard_interval_basic hx).2
  dsimp [lam, kappa]
  linarith

/-- An explicit compact interval, stronger than the qualitative compactness assertion. -/
theorem qChoice_range {x : ℝ} (hx : hardInterval x) :
    (4001 : ℝ) / 1000 ≤ qChoice x ∧ qChoice x ≤ (9 : ℝ) / 2 := by
  have hk := kappa_pos hx
  have hl := lam_pos hx
  have hratio : (1 : ℝ) / 1000 ≤ lam x / kappa x := by
    apply (le_div_iff₀ hk).2
    obtain ⟨hxl, hxu⟩ := hx
    have ht := theta_lower
    dsimp [kappa, lam]
    linarith
  unfold qChoice
  split_ifs with ht
  · have hreg := first_region ht
    have hup : lam x / kappa x ≤ (1 : ℝ) / 2 := by
      apply (div_le_iff₀ hk).2
      linarith
    constructor <;> linarith
  · constructor <;> norm_num

theorem qChoice_gt_four {x : ℝ} (hx : hardInterval x) : 4 < qChoice x := by
  have h := (qChoice_range hx).1
  linarith

/-- The first-spacing restrictions, equation (6.12). -/
theorem qChoice_spacing_conditions {x : ℝ} (hx : hardInterval x) :
    (qChoice x - 4) * kappa x ≤ lam x ∧
    (3 * qChoice x - 8) * lam x ≤ (8 - qChoice x) * kappa x := by
  have hk := kappa_pos hx
  have hl := lam_pos hx
  unfold qChoice
  split_ifs with ht
  · have hreg := first_region ht
    have hratio : (lam x / kappa x) * kappa x = lam x :=
      div_mul_cancel₀ _ (ne_of_gt hk)
    constructor
    · nlinarith
    · have hmul := mul_nonneg (sub_nonneg.mpr hreg)
        (show 0 ≤ 4 * kappa x + 3 * lam x by linarith)
      have hp : 0 ≤ 4 * kappa x ^ 2 - 5 * kappa x * lam x - 3 * lam x ^ 2 := by
        nlinarith [sq_nonneg (lam x)]
      apply (mul_le_mul_iff_left₀ hk).mp
      nlinarith [mul_pos hk hl]
  · have hreg := second_region (le_of_lt (lt_of_not_ge ht))
    have hlow := lower_ratio hx
    constructor <;> nlinarith

theorem E_first_identity {x : ℝ} (hx : hardInterval x) :
    E x (4 + lam x / kappa x) = E1 x := by
  have hk := kappa_pos hx
  have hl := lam_pos hx
  have hd := denominator_neg hx
  have hd' : x * 632 + 137 ≠ 0 := by linarith
  dsimp only [E, E1]
  field_simp (disch := first | positivity | (apply ne_of_lt; linarith))
  field_simp [hd']
  dsimp [kappa, lam]
  ring

theorem E_second_identity (x : ℝ) : E x (9 / 2) = E2 x := by
  dsimp [E, E2]
  ring

/-- The double-root identity proving the interior maximum, equation (6.18). -/
theorem E1_square_identity {x : ℝ} (hx : hardInterval x) :
    E1 x - theta = (276 / 5 : ℝ) * (x - x0) ^ 2 / (632 * x + 137) := by
  have hd := denominator_neg hx
  have hd' : x * 632 + 137 ≠ 0 := by linarith
  have hz := zero_discriminant
  dsimp [E1, x0]
  field_simp (disch := first | positivity | (apply ne_of_lt; linarith))
  field_simp [hd']
  nlinarith

theorem E1_le_theta {x : ℝ} (hx : hardInterval x) : E1 x ≤ theta := by
  have hid := E1_square_identity hx
  have hnum : 0 ≤ (276 / 5 : ℝ) * (x - x0) ^ 2 := by positivity
  have hquot := div_nonpos_of_nonneg_of_nonpos hnum (le_of_lt (denominator_neg hx))
  linarith

theorem E2_strictMono : StrictMono E2 := by
  intro a b hab
  dsimp [E2]
  linarith

theorem E2_endpoint_equivalence : E2 (-theta) ≤ theta ↔ (573 : ℝ) / 1828 ≤ theta := by
  dsimp [E2]
  constructor <;> intro h <;> linarith

theorem E2_endpoint_strict : E2 (-theta) < theta := by
  have h := theta_lower
  dsimp [E2]
  linarith

theorem E2_lt_theta {x : ℝ} (hx : hardInterval x) : E2 x < theta := by
  have hm := E2_strictMono.monotone hx.2
  exact lt_of_le_of_lt hm E2_endpoint_strict

/-- The optimized exponent is bounded throughout the full hard interval. -/
theorem optimized_exponent_le_theta {x : ℝ} (hx : hardInterval x) :
    E x (qChoice x) ≤ theta := by
  unfold qChoice
  split_ifs
  · rw [E_first_identity hx]
    exact E1_le_theta hx
  · rw [E_second_identity]
    exact le_of_lt (E2_lt_theta hx)

theorem x0_mem_hardInterval : hardInterval x0 := by
  obtain ⟨hlo, hmid, hhi⟩ := x0_location
  exact ⟨hlo, le_of_lt (lt_trans hmid hhi)⟩

theorem optimized_exponent_at_x0 : E x0 (qChoice x0) = theta := by
  have hloc := x0_location
  have hx := x0_mem_hardInterval
  unfold qChoice
  rw [if_pos (le_of_lt hloc.2.1), E_first_identity hx]
  have hid := E1_square_identity hx
  simp only [sub_self, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_div] at hid
  linarith

/-- A single formal statement of Lemma 6.2 and the exponent bound used in Proposition 6.3. -/
theorem hard_interval_optimization {x : ℝ} (hx : hardInterval x) :
    0 < lam x ∧ 0 < kappa x ∧ lam x ≤ kappa x ∧
    (4001 : ℝ) / 1000 ≤ qChoice x ∧ qChoice x ≤ (9 : ℝ) / 2 ∧
    (qChoice x - 4) * kappa x ≤ lam x ∧
    (3 * qChoice x - 8) * lam x ≤ (8 - qChoice x) * kappa x ∧
    E x (qChoice x) ≤ theta := by
  exact ⟨lam_pos hx, kappa_pos hx, lam_le_kappa hx,
    (qChoice_range hx).1, (qChoice_range hx).2,
    (qChoice_spacing_conditions hx).1, (qChoice_spacing_conditions hx).2,
    optimized_exponent_le_theta hx⟩

end

end CircleDivisor.Optimization
