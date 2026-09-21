import CircleDivisor.ScaleExponents

/-! Exact scale comparisons for the stronger paired energy. Here all variables
are logarithms; the real-power translation is in `ScaleBounds`. -/

namespace CircleDivisor.EnergyV3.ScaleExponents
noncomputable section
open CircleDivisor.ScaleExponents

def crossEnergy (k l s : ℝ) : ℝ :=
  min (k + l + totalDensity k l s) (max (2 * k + l) (s + 5 * k / 2 + l / 2))

def crossExponent (k l ρ : ℝ) : ℝ := (2 + 2 * ρ) * k + (1 + 2 * ρ) * l

theorem cross_ray_large {k l s ρ : ℝ} (hsk : -k / 2 ≤ s) (hsl : -l ≤ s)
    (hs0 : s ≤ 0) (hρ : ρ ≤ 1) :
    crossEnergy k l s + ρ * (totalDensity k l s - 2 * s) ≤ rootExponent k l ρ := by
  have he := min_le_left (k + l + totalDensity k l s) (max (2 * k + l) (s + 5 * k / 2 + l / 2))
  change crossEnergy k l s ≤ _ at he
  rw [total_density_large hsk hsl] at he ⊢
  unfold rootExponent
  nlinarith [mul_nonneg (sub_nonneg.mpr hρ) (neg_nonneg.mpr hs0)]

theorem cross_ray_mid_radial {k l s ρ : ℝ} (hsk : s ≤ -k / 2) (hsl : -l ≤ s)
    (hρ0 : 0 ≤ ρ) :
    crossEnergy k l s + ρ * (totalDensity k l s - 2 * s) ≤ secondExponent k l ρ := by
  have he := min_le_left (k + l + totalDensity k l s) (max (2 * k + l) (s + 5 * k / 2 + l / 2))
  change crossEnergy k l s ≤ _ at he
  rw [total_density_mid_radial hsk hsl] at he ⊢
  unfold secondExponent
  nlinarith [mul_nonneg (show 0 ≤ 1 + 3 * ρ by linarith) (show 0 ≤ s + l by linarith)]

theorem cross_ray_mid_angular {k l s ρ : ℝ} (hl : 0 ≤ l)
    (hsk : -k / 2 ≤ s) (hsl : s ≤ -l) (hρ0 : 0 ≤ ρ) :
    crossEnergy k l s + ρ * (totalDensity k l s - 2 * s) ≤ crossExponent k l ρ := by
  have he := min_le_left (k + l + totalDensity k l s) (max (2 * k + l) (s + 5 * k / 2 + l / 2))
  change crossEnergy k l s ≤ _ at he
  rw [total_density_mid_angular hsk hsl] at he ⊢
  unfold crossExponent
  nlinarith [mul_nonneg hρ0 (show 0 ≤ k + 2 * s by linarith), mul_nonneg hl hρ0]

theorem cross_ray_small {k l s ρ : ℝ} (hl : 0 ≤ l)
    (hsk : s ≤ -k / 2) (hsl : s ≤ -l) (hslow : -(k + l) / 2 ≤ s)
    (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 1 / 4) :
    crossEnergy k l s + ρ * (totalDensity k l s - 2 * s) ≤
      max (rootExponent k l ρ) (crossExponent k l ρ) := by
  have he := min_le_right (k + l + totalDensity k l s) (max (2 * k + l) (s + 5 * k / 2 + l / 2))
  change crossEnergy k l s ≤ _ at he
  rw [total_density_small hsk hsl]
  apply le_trans (add_le_add_left he _)
  rw [← max_add_add_right]
  apply max_le
  · apply le_trans _ (le_max_right _ _)
    unfold crossExponent
    nlinarith [mul_nonneg hρ0 (show 0 ≤ s + (k + l) / 2 by linarith)]
  · rcases le_total (2 * l) k with hkl | hkl
    · apply le_trans _ (le_max_right _ _)
      unfold crossExponent
      nlinarith [mul_nonneg (show 0 ≤ 1 - 4 * ρ by linarith)
        (show 0 ≤ -k / 2 - s by linarith),
        mul_nonneg hl (show 0 ≤ 1 / 2 + 2 * ρ by linarith)]
    · apply le_trans _ (le_max_left _ _)
      unfold rootExponent
      nlinarith [mul_nonneg (show 0 ≤ 1 - 4 * ρ by linarith)
        (show 0 ≤ -l - s by linarith),
        mul_nonneg (show 0 ≤ 1 / 2 - ρ by linarith) (show 0 ≤ 2 * l - k by linarith),
        mul_nonneg hl (show 0 ≤ 3 / 2 - ρ by linarith)]

theorem cross_ray_bound {k l s ρ : ℝ} (hl : 0 ≤ l) (hs0 : s ≤ 0)
    (hslow : -(k + l) / 2 ≤ s) (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 1 / 4) :
    crossEnergy k l s + ρ * (totalDensity k l s - 2 * s) ≤
      max (rootExponent k l ρ) (max (secondExponent k l ρ) (crossExponent k l ρ)) := by
  rcases le_total (-k / 2) s with hk | hk <;> rcases le_total (-l) s with hl' | hl'
  · exact (cross_ray_large hk hl' hs0 (by linarith)).trans (le_max_left _ _)
  · exact (cross_ray_mid_angular hl hk hl' hρ0).trans
      ((le_max_right _ _).trans (le_max_right _ _))
  · exact (cross_ray_mid_radial hk hl' hρ0).trans
      ((le_max_left _ _).trans (le_max_right _ _))
  · exact (cross_ray_small hl hk hl' hslow hρ0 hρ).trans
      (max_le_max_left _ (le_max_right _ _))

end
end CircleDivisor.EnergyV3.ScaleExponents
