import Mathlib

/-! Exact exponent inequalities in Section 4.2–4.3.

`k`, `l` and `s` denote logarithms of `K`, `L` and the angular scale in
any common base greater than one. The statements here concern exponents,
and do not assert that the analytic moment estimates have been proved.
-/

namespace CircleDivisor.ScaleExponents

noncomputable section

def sameDensity (k l s : ℝ) : ℝ := max (s + k + l) (l - s)

def totalDensity (k l s : ℝ) : ℝ :=
  max (max (s + k + l) k) (max (l - s) (-2 * s))

def sameEnergy (k l s : ℝ) : ℝ :=
  min (k + l + sameDensity k l s) (max (s + 2 * (k + l)) (k + 3 * l))

def crossEnergy (k l s : ℝ) : ℝ :=
  min (k + l + totalDensity k l s) (k + l + 2 * s + 2 * k + l)

def rootExponent (k l ρ : ℝ) : ℝ := (2 + ρ) * (k + l)
def secondExponent (k l ρ : ℝ) : ℝ := k + (3 + 4 * ρ) * l
def crossExponent (k l ρ : ℝ) : ℝ := (2 + 2 * ρ) * k + (3 / 2 + ρ) * l
def radialExponent (k l ρ : ℝ) : ℝ := (1 + 3 * ρ / 2) * k + (3 + 5 * ρ / 2) * l

theorem same_density_large {k l s : ℝ} (hs : -k / 2 ≤ s) :
    sameDensity k l s = s + k + l := by
  unfold sameDensity
  rw [max_eq_left (by linarith)]

theorem same_density_small {k l s : ℝ} (hs : s ≤ -k / 2) :
    sameDensity k l s = l - s := by
  unfold sameDensity
  rw [max_eq_right (by linarith)]

theorem same_ray_large {k l s ρ : ℝ} (hs : -k / 2 ≤ s) (hs0 : s ≤ 0)
    (hρ : ρ ≤ 1) :
    sameEnergy k l s + ρ * (sameDensity k l s - 2 * s) ≤ rootExponent k l ρ := by
  have he := min_le_left (k + l + sameDensity k l s)
    (max (s + 2 * (k + l)) (k + 3 * l))
  rw [same_density_large hs] at he ⊢
  unfold sameEnergy at *
  rw [same_density_large hs] at *
  unfold rootExponent
  nlinarith [mul_nonneg (sub_nonneg.mpr hρ) (neg_nonneg.mpr hs0)]

theorem same_ray_small {k l s ρ : ℝ} (hk : 0 ≤ k)
    (hs : s ≤ -k / 2) (hslow : -(k + l) / 2 ≤ s)
    (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 1 / 4) :
    sameEnergy k l s + ρ * (sameDensity k l s - 2 * s) ≤
      max (rootExponent k l ρ) (radialExponent k l ρ) := by
  have he := min_le_right (k + l + sameDensity k l s)
    (max (s + 2 * (k + l)) (k + 3 * l))
  change sameEnergy k l s ≤ _ at he
  rw [same_density_small hs]
  apply le_trans (add_le_add_left he _)
  rw [← max_add_add_right]
  apply max_le
  · apply le_trans _ (le_max_left _ _)
    unfold rootExponent
    nlinarith [mul_nonneg (show 0 ≤ 1 - 3 * ρ by linarith)
      (show 0 ≤ -k / 2 - s by linarith),
      mul_nonneg hk (show 0 ≤ 1 - ρ by linarith)]
  · apply le_trans _ (le_max_right _ _)
    unfold radialExponent
    nlinarith [mul_nonneg hρ0 (show 0 ≤ s + (k + l) / 2 by linarith)]

/-- The same-ray summand has precisely the first/fourth monomial exponents. -/
theorem same_ray_bound {k l s ρ : ℝ} (hk : 0 ≤ k) (hs0 : s ≤ 0)
    (hslow : -(k + l) / 2 ≤ s) (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 1 / 4) :
    sameEnergy k l s + ρ * (sameDensity k l s - 2 * s) ≤
      max (rootExponent k l ρ) (radialExponent k l ρ) := by
  rcases le_total (-k / 2) s with hs | hs
  · exact (same_ray_large hs hs0 (by linarith)).trans (le_max_left _ _)
  · exact same_ray_small hk hs hslow hρ0 hρ

theorem total_density_large {k l s : ℝ} (hsk : -k / 2 ≤ s) (hsl : -l ≤ s) :
    totalDensity k l s = s + k + l := by
  unfold totalDensity
  rw [max_eq_left (by linarith : k ≤ s + k + l)]
  apply max_eq_left
  apply max_le <;> linarith

theorem total_density_mid_radial {k l s : ℝ} (hsk : s ≤ -k / 2) (hsl : -l ≤ s) :
    totalDensity k l s = l - s := by
  unfold totalDensity
  rw [max_eq_left (by linarith : -2 * s ≤ l - s)]
  apply max_eq_right
  apply max_le <;> linarith

theorem total_density_mid_angular {k l s : ℝ} (hsk : -k / 2 ≤ s) (hsl : s ≤ -l) :
    totalDensity k l s = k := by
  unfold totalDensity
  rw [max_eq_right (by linarith : s + k + l ≤ k)]
  apply max_eq_left
  apply max_le <;> linarith

theorem total_density_small {k l s : ℝ} (hsk : s ≤ -k / 2) (hsl : s ≤ -l) :
    totalDensity k l s = -2 * s := by
  unfold totalDensity
  rw [max_eq_right (by linarith : l - s ≤ -2 * s)]
  apply max_eq_right
  apply max_le <;> linarith

theorem cross_ray_large {k l s ρ : ℝ} (hsk : -k / 2 ≤ s) (hsl : -l ≤ s)
    (hs0 : s ≤ 0) (hρ : ρ ≤ 1) :
    crossEnergy k l s + ρ * (totalDensity k l s - 2 * s) ≤ rootExponent k l ρ := by
  have he := min_le_left (k + l + totalDensity k l s) (k + l + 2 * s + 2 * k + l)
  change crossEnergy k l s ≤ _ at he
  rw [total_density_large hsk hsl] at he ⊢
  unfold rootExponent
  nlinarith [mul_nonneg (sub_nonneg.mpr hρ) (neg_nonneg.mpr hs0)]

theorem cross_ray_mid_radial {k l s ρ : ℝ} (hsk : s ≤ -k / 2) (hsl : -l ≤ s)
    (hρ0 : 0 ≤ ρ) :
    crossEnergy k l s + ρ * (totalDensity k l s - 2 * s) ≤ secondExponent k l ρ := by
  have he := min_le_left (k + l + totalDensity k l s) (k + l + 2 * s + 2 * k + l)
  change crossEnergy k l s ≤ _ at he
  rw [total_density_mid_radial hsk hsl] at he ⊢
  unfold secondExponent
  nlinarith [mul_nonneg (show 0 ≤ 1 + 3 * ρ by linarith) (show 0 ≤ s + l by linarith)]

theorem cross_ray_mid_angular {k l s ρ : ℝ} (hl : 0 ≤ l)
    (hsk : -k / 2 ≤ s) (hsl : s ≤ -l) (hρ0 : 0 ≤ ρ) :
    crossEnergy k l s + ρ * (totalDensity k l s - 2 * s) ≤ crossExponent k l ρ := by
  have he := min_le_left (k + l + totalDensity k l s) (k + l + 2 * s + 2 * k + l)
  change crossEnergy k l s ≤ _ at he
  rw [total_density_mid_angular hsk hsl] at he ⊢
  unfold crossExponent
  nlinarith [mul_nonneg hρ0 (show 0 ≤ k + 2 * s by linarith),
    mul_nonneg hl (show 0 ≤ 1 / 2 + ρ by linarith)]

/-- The crossing scale `log s_c = -k/2-l/4` controls the minimum on all scales. -/
theorem cross_ray_small {k l s ρ : ℝ} (hsk : s ≤ -k / 2) (hsl : s ≤ -l)
    (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 1 / 4) :
    crossEnergy k l s + ρ * (totalDensity k l s - 2 * s) ≤ crossExponent k l ρ := by
  by_cases hsc : s ≤ -k / 2 - l / 4
  · have he := min_le_right (k + l + totalDensity k l s) (k + l + 2 * s + 2 * k + l)
    change crossEnergy k l s ≤ _ at he
    rw [total_density_small hsk hsl]
    unfold crossExponent
    nlinarith [mul_nonneg (show 0 ≤ 2 - 4 * ρ by linarith)
      (show 0 ≤ -k / 2 - l / 4 - s by linarith)]
  · have he := min_le_left (k + l + totalDensity k l s) (k + l + 2 * s + 2 * k + l)
    change crossEnergy k l s ≤ _ at he
    rw [total_density_small hsk hsl] at he ⊢
    unfold crossExponent
    nlinarith [mul_nonneg (show 0 ≤ 2 + 4 * ρ by linarith)
      (show 0 ≤ s + k / 2 + l / 4 by linarith)]

/-- All three angular regimes, including either ordering of `K^(1/2)` and `L`. -/
theorem cross_ray_bound {k l s ρ : ℝ} (hl : 0 ≤ l) (hs0 : s ≤ 0)
    (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 1 / 4) :
    crossEnergy k l s + ρ * (totalDensity k l s - 2 * s) ≤
      max (rootExponent k l ρ) (max (secondExponent k l ρ) (crossExponent k l ρ)) := by
  rcases le_total (-k / 2) s with hk | hk <;> rcases le_total (-l) s with hl' | hl'
  · exact (cross_ray_large hk hl' hs0 (by linarith)).trans (le_max_left _ _)
  · exact (cross_ray_mid_angular hl hk hl' hρ0).trans
      ((le_max_right _ _).trans (le_max_right _ _))
  · exact (cross_ray_mid_radial hk hl' hρ0).trans
      ((le_max_left _ _).trans (le_max_right _ _))
  · exact (cross_ray_small hk hl' hρ0 hρ).trans
      ((le_max_right _ _).trans (le_max_right _ _))

end
end CircleDivisor.ScaleExponents
