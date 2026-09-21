import Mathlib

/-! The exact normalized cone and adapted linear coordinates, (1.12), (2.10).
These are algebraic facts; no Fourier localization theorem is assumed here. -/

namespace CircleDivisor.ConeGeometry
noncomputable section

abbrev Space := Fin 3 → ℝ

def coneParam (r t : ℝ) : Space := ![r, r * t, r * t ^ 2]

def circularMap (v : Space) : Space :=
  ![(3 / 5) * v 1, (3 / 5) * ((v 2 - v 0) / 2), (3 / 5) * ((v 2 + v 0) / 2)]

def circularInverse (v : Space) : Space :=
  ![(5 / 3) * (v 2 - v 1), (5 / 3) * v 0, (5 / 3) * (v 2 + v 1)]

theorem circular_left_inverse (v : Space) : circularInverse (circularMap v) = v := by
  ext i
  fin_cases i <;> simp [circularInverse, circularMap] <;> ring

theorem circular_right_inverse (v : Space) : circularMap (circularInverse v) = v := by
  ext i
  fin_cases i <;> simp [circularInverse, circularMap] <;> ring

theorem circularMap_injective : Function.Injective circularMap := by
  intro v w h
  have hh := congrArg circularInverse h
  simpa only [circular_left_inverse] using hh

theorem circular_cone (r t : ℝ) :
    (circularMap (coneParam r t) 0) ^ 2 + (circularMap (coneParam r t) 1) ^ 2 =
      (circularMap (coneParam r t) 2) ^ 2 := by
  simp [circularMap, coneParam]
  ring

theorem radial_truncation {r t : ℝ} (hr : 1 ≤ r) (hr' : r < 2)
    (ht : 1 ≤ t ^ 2) (ht' : t ^ 2 < 2) :
    3 / 5 ≤ circularMap (coneParam r t) 2 ∧
      circularMap (coneParam r t) 2 < 9 / 5 := by
  change 3 / 5 ≤ (3 / 5) * ((r * t ^ 2 + r) / 2) ∧
    (3 / 5) * ((r * t ^ 2 + r) / 2) < 9 / 5
  constructor
  · nlinarith [mul_nonneg (show 0 ≤ r by linarith) (show 0 ≤ t ^ 2 - 1 by linarith)]
  · nlinarith [mul_pos (show 0 < r by linarith) (show 0 < 2 - t ^ 2 by linarith)]

def frequency (K L k l : ℝ) : Space :=
  ![l / L, l / L * Real.sqrt (k / K), k * l / (K * L)]

theorem frequency_eq_coneParam {K L k l : ℝ} (hK : 0 < K) (_hL : 0 < L)
    (hk : 0 ≤ k) :
    frequency K L k l = coneParam (l / L) (Real.sqrt (k / K)) := by
  have hsq := Real.sq_sqrt (div_nonneg hk (le_of_lt hK))
  ext i
  fin_cases i <;> simp [frequency, coneParam, hsq]
  ring

theorem frequency_on_circular_cone {K L k l : ℝ} (hK : 0 < K) (hL : 0 < L)
    (hk : 0 ≤ k) :
    (circularMap (frequency K L k l) 0) ^ 2 +
      (circularMap (frequency K L k l) 1) ^ 2 =
      (circularMap (frequency K L k l) 2) ^ 2 := by
  rw [frequency_eq_coneParam hK hL hk]
  exact circular_cone _ _

def adapted (t₀ : ℝ) (v : Space) : Space :=
  ![v 0, v 1 - t₀ * v 0, v 2 - 2 * t₀ * v 1 + t₀ ^ 2 * v 0]

def adaptedInverse (t₀ : ℝ) (v : Space) : Space :=
  ![v 0, v 1 + t₀ * v 0, v 2 + 2 * t₀ * v 1 + t₀ ^ 2 * v 0]

theorem adapted_coneParam (r t t₀ : ℝ) :
    adapted t₀ (coneParam r t) = ![r, r * (t - t₀), r * (t - t₀) ^ 2] := by
  ext i
  fin_cases i <;> simp [adapted, coneParam] <;> ring

theorem adapted_left_inverse (t₀ : ℝ) (v : Space) :
    adaptedInverse t₀ (adapted t₀ v) = v := by
  ext i
  fin_cases i <;> simp [adaptedInverse, adapted]
  ring

theorem adapted_sub (t₀ : ℝ) (v w : Space) :
    adapted t₀ (v - w) = adapted t₀ v - adapted t₀ w := by
  ext i
  fin_cases i <;> simp [adapted] <;> ring

/-- The implication behind the first neighbor-count step, with explicit constants. -/
theorem parameter_separation {r r' t t' t₀ s A B : ℝ}
    (hr : 1 ≤ r) (_hs : 0 ≤ s)
    (hangle : |t' - t₀| ≤ s) (hradial : |r - r'| ≤ A)
    (hlinear : |r * (t - t₀) - r' * (t' - t₀)| ≤ B) :
    |t - t'| ≤ B + A * s := by
  have hA : 0 ≤ A := (abs_nonneg _).trans hradial
  have hid : r * (t - t') =
      (r * (t - t₀) - r' * (t' - t₀)) - (r - r') * (t' - t₀) := by ring
  have hh : |r * (t - t')| ≤ B + A * s := by
    rw [hid]
    calc
      _ ≤ |r * (t - t₀) - r' * (t' - t₀)| + |(r - r') * (t' - t₀)| := abs_sub _ _
      _ ≤ B + A * s := by
        rw [abs_mul]
        exact add_le_add hlinear (mul_le_mul hradial hangle (abs_nonneg _) hA)
  rw [abs_mul, abs_of_nonneg (show 0 ≤ r by linarith)] at hh
  nlinarith [abs_nonneg (t - t')]

end
end CircleDivisor.ConeGeometry
