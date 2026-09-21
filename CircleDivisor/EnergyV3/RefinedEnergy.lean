import CircleDivisor.EnergyV3.EnvelopeEnergies

/-! The actual widths `W=A sqrt(K/L)` and `V=A s K` in the refined
same-ray and cross-ray energy estimates. -/

namespace CircleDivisor.EnergyV3.RefinedEnergy
noncomputable section
open MeasureTheory GuthMaldague FourierLocalization FourierEnergy PairEnergies EnvelopeEnergies
open scoped BigOperators FourierTransform
abbrev Space := FourierLocalization.Space

theorem widths {K L s A : ℝ} (hL : 1 ≤ L) (hLK : L ≤ K)
    (hs : 1 / Real.sqrt (K * L) ≤ s) (hA : 1 ≤ A) :
    1 ≤ A * Real.sqrt (K / L) ∧ 1 ≤ A * s * K ∧ A * Real.sqrt (K / L) ≤ A * K := by
  have hL0 : 0 < L := by linarith
  have hK0 : 0 < K := by linarith
  have hKL : 0 < K * L := mul_pos hK0 hL0
  have hroot := Real.sq_sqrt (show 0 ≤ K / L by positivity)
  have hrootKL := Real.sq_sqrt hKL.le
  have hr1 : 1 ≤ Real.sqrt (K / L) := by
    have hh : 1 ≤ K / L := (le_div_iff₀ hL0).mpr (by simpa using hLK)
    nlinarith [Real.sqrt_nonneg (K / L)]
  have hrK : Real.sqrt (K * L) ≤ K := by nlinarith [Real.sqrt_nonneg (K * L)]
  have hsK : 1 ≤ s * K := by
    have hrr : 0 < Real.sqrt (K * L) := Real.sqrt_pos.mpr hKL
    have hh := hs.trans' (one_div_le_one_div_of_le hrr hrK)
    exact (div_le_iff₀ hK0).mp hh
  have hr2 : Real.sqrt (K / L) ≤ K := by
    have hP : 1 ≤ K * L := one_le_mul_of_one_le_of_one_le (hL.trans hLK) hL
    have hh : K / L ≤ K ^ 2 := (div_le_iff₀ hL0).mpr (by nlinarith)
    nlinarith [Real.sqrt_nonneg (K / L)]
  exact ⟨one_le_mul_of_one_le_of_one_le hA hr1,
    by simpa [mul_assoc] using one_le_mul_of_one_le_of_one_le hA hsK,
    mul_le_mul_of_nonneg_left hr2 (by linarith)⟩

theorem cross_width_identity {K L s A : ℝ} (hK : 0 < K) (hL : 0 < L) :
    K * ((A * Real.sqrt (K / L)) ^ 2 * L ^ 2 + (A * s * K) * (A * Real.sqrt (K / L)) * L) =
      A ^ 2 * (K ^ 2 * L + s * K ^ (5 / 2 : ℝ) * L ^ (1 / 2 : ℝ)) := by
  have hroot : Real.sqrt (K / L) ^ 2 = K / L := Real.sq_sqrt (by positivity)
  have hfirst : Real.sqrt (K / L) ^ 2 * L ^ 2 = K * L := by rw [hroot]; field_simp
  have hsecond : Real.sqrt (K / L) * L = Real.sqrt (K * L) := by
    have hs := Real.sq_sqrt (mul_pos hK hL).le
    nlinarith [Real.sqrt_nonneg (K / L), Real.sqrt_nonneg (K * L),
      mul_nonneg (Real.sqrt_nonneg (K / L)) hL.le]
  have hpower : K ^ 2 * Real.sqrt (K * L) = K ^ (5 / 2 : ℝ) * L ^ (1 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow, Real.mul_rpow hK.le hL.le,
      show K ^ (2 : ℕ) = K ^ (2 : ℝ) by simp, ← mul_assoc, ← Real.rpow_add hK]
    norm_num
  calc
    _ = A ^ 2 * (K * (Real.sqrt (K / L) ^ 2 * L ^ 2) + s * K ^ 2 * (Real.sqrt (K / L) * L)) := by ring
    _ = A ^ 2 * (K ^ 2 * L + s * (K ^ 2 * Real.sqrt (K * L))) := by rw [hfirst, hsecond]; ring
    _ = _ := by rw [hpower]; ring

theorem same_width_bound {K L s A : ℝ} (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hs : 0 ≤ s) (hA : 1 ≤ A) :
    K * (A * s * K) * L ^ 2 + K * L ^ 3 ≤ A * (s * (K * L) ^ 2 + K * L ^ 3) := by
  nlinarith [mul_nonneg (show 0 ≤ A-1 by linarith) (show 0 ≤ K * L ^ 3 by positivity)]

def familyEnergy (n j : ℕ) (e : Space ≃L[ℝ] Space) (K L : ℝ)
    (χ : SchwartzMap Space ℂ) (a : Point → ℂ) (P : CapIndex j → Finset Pair) : ℝ :=
  ∑ i : CapIndex j, ∑' m : Lattice, envelopeVolume n j i m *
    ‖envelopePairAverage n j i (fun y => localizedPair K L χ a (P i) (e y)) m‖ ^ 2

theorem familyEnergy_le (n j : ℕ) (e : Space ≃L[ℝ] Space) (K L c E : ℝ)
    (hK : 1 ≤ K) (hL : 0 < L) (hc : 4 * c ≤ 1)
    (χ : SchwartzMap Space ℂ)
    (hχ : Function.support (𝓕 (χ : Space → ℂ)) ⊆ Metric.ball 0 c)
    (a : Point → ℂ) (ha : ∀ p, ‖a p‖ ≤ 1) (P : CapIndex j → Finset Pair)
    (henergy : (∑ i : CapIndex j, (∫ x, ‖localizedPair K L χ a (P i) x‖ ^ 2) / (K * L) ^ 3) ≤ E) :
    familyEnergy n j e K L χ a P ≤ overlapBound * LinearTransport.jacobian e * E * (K * L) ^ 3 := by
  have hh := (transported_family_average_energy n j P e K L c hK hL hc χ hχ a ha).trans
    (mul_le_mul_of_nonneg_left henergy (mul_nonneg overlapBound_nonneg (LinearTransport.jacobian_pos e).le))
  rw [← Finset.sum_div] at hh
  exact (div_le_iff₀ (show 0 < (K * L) ^ 3 by positivity)).mp hh

theorem same_familyEnergy (n j : ℕ) (e : Space ≃L[ℝ] Space) (K L s A c : ℝ)
    (hL : 1 ≤ L) (hLK : L ≤ K) (hs : 1 / Real.sqrt (K * L) ≤ s) (hA : 1 ≤ A) (hc : 4 * c ≤ 1)
    (χ : SchwartzMap Space ℂ)
    (hχ : Function.support (𝓕 (χ : Space → ℂ)) ⊆ Metric.ball 0 c)
    (a : Point → ℂ) (ha : ∀ p, ‖a p‖ ≤ 1) (P : CapIndex j → Finset Pair)
    (hdisj : ((Finset.univ : Finset (CapIndex j)) : Set (CapIndex j)).PairwiseDisjoint P)
    (hP : ∀ i, SameWindow K L (A * s * K) (P i)) :
    familyEnergy n j e K L χ a P ≤
      (48 * A * overlapBound * LinearTransport.jacobian e * (∫ x, ‖χ x‖ ^ 4)) *
        (K * L) ^ 3 * (s * (K * L) ^ 2 + K * L ^ 3) := by
  have hK : 1 ≤ K := hL.trans hLK
  have hK0 : 0 < K := by linarith
  have hL0 : 0 < L := by linarith
  have hs0 : 0 < s := (one_div_pos.mpr (Real.sqrt_pos.mpr (mul_pos hK0 hL0))).trans_le hs
  have hw := widths hL hLK hs hA
  have he := localized_same_energy_family Finset.univ P hdisj K L (A*s*K) c
    hK hL hw.2.1 hc (fun i _ => hP i) χ hχ a ha
  have hm := familyEnergy_le n j e K L c _ hK hL0 hc χ hχ a ha P he
  have hn := same_width_bound hK0.le hL0.le hs0.le hA
  have hCJ : 0 ≤ overlapBound * LinearTransport.jacobian e :=
    mul_nonneg overlapBound_nonneg (LinearTransport.jacobian_pos e).le
  calc
    _ ≤ _ := hm
    _ ≤ overlapBound * LinearTransport.jacobian e *
        ((∫ x, ‖χ x‖ ^ 4) * (48 * (A * (s * (K * L) ^ 2 + K * L ^ 3)))) * (K * L) ^ 3 := by
      gcongr
    _ = _ := by ring

theorem cross_familyEnergy (n j : ℕ) (e : Space ≃L[ℝ] Space) (K L s A c γ C : ℝ)
    (hL : 1 ≤ L) (hLK : L ≤ K) (hs : 1 / Real.sqrt (K * L) ≤ s) (hA : 1 ≤ A) (hc : 4 * c ≤ 1)
    (hγ : 0 ≤ γ) (hC : 1 ≤ C) (hdiv : SpacingCount.NaturalDivisorEstimate γ C)
    (χ : SchwartzMap Space ℂ)
    (hχ : Function.support (𝓕 (χ : Space → ℂ)) ⊆ Metric.ball 0 c)
    (a : Point → ℂ) (ha : ∀ p, ‖a p‖ ≤ 1) (P : CapIndex j → Finset Pair)
    (hdisj : ((Finset.univ : Finset (CapIndex j)) : Set (CapIndex j)).PairwiseDisjoint P)
    (hP : ∀ i, CrossWindow K L (A * Real.sqrt (K/L)) (A * s * K) (P i)) :
    familyEnergy n j e K L χ a P ≤
      ((576 * (1 + 2 * C * (16 * A) ^ γ)) * A ^ 2 * overlapBound *
        LinearTransport.jacobian e * (∫ x, ‖χ x‖ ^ 4)) *
          (K * L) ^ (3 + γ) * (K ^ 2 * L + s * K ^ (5 / 2 : ℝ) * L ^ (1 / 2 : ℝ)) := by
  have hK : 1 ≤ K := hL.trans hLK
  have hK0 : 0 < K := by linarith
  have hL0 : 0 < L := by linarith
  have hw := widths hL hLK hs hA
  have he := localized_cross_energy_family Finset.univ P hdisj K L (A*Real.sqrt (K/L)) (A*s*K) A c
    hK hL hw.1 hw.2.1 hA hw.2.2 hc γ C hγ hC hdiv (fun i _ => hP i) χ hχ a ha
  have hm := familyEnergy_le n j e K L c _ hK hL0 hc χ hχ a ha P he
  have hid := cross_width_identity (s := s) (A := A) hK0 hL0
  have hp : (K * L) ^ (3 + γ) = (K * L) ^ (3 : ℕ) * (K * L) ^ γ := by
    rw [Real.rpow_add (mul_pos hK0 hL0)]
    norm_num
  apply hm.trans_eq
  rw [hp]
  calc
    _ = (overlapBound * LinearTransport.jacobian e * (∫ x, ‖χ x‖ ^ 4) *
        (576 * (1 + 2 * C * (16 * A) ^ γ)) * (K * L) ^ γ * (K * L) ^ (3 : ℕ)) *
          (K * ((A * Real.sqrt (K / L)) ^ 2 * L ^ 2 + (A * s * K) * (A * Real.sqrt (K / L)) * L)) := by ring
    _ = _ := by rw [hid]; ring

/-- Real summability has been proved for these actual localized averages,
so the extended nonnegative sum used by amplitude integration agrees with
the real-valued family energy. -/
theorem familyEnergy_ofReal (n j : ℕ) (e : Space ≃L[ℝ] Space) (K L c : ℝ)
    (hK : 1 ≤ K) (hL : 0 < L) (hc : 4 * c ≤ 1)
    (χ : SchwartzMap Space ℂ)
    (hχ : Function.support (𝓕 (χ : Space → ℂ)) ⊆ Metric.ball 0 c)
    (a : Point → ℂ) (ha : ∀ p, ‖a p‖ ≤ 1) (P : CapIndex j → Finset Pair) :
    ENNReal.ofReal (familyEnergy n j e K L χ a P) =
      ∑ i : CapIndex j, ∑' m : Lattice, ENNReal.ofReal (envelopeVolume n j i m *
        ‖envelopePairAverage n j i (fun y => localizedPair K L χ a (P i) (e y)) m‖ ^ 2) := by
  have hnn (i : CapIndex j) (m : Lattice) : 0 ≤ envelopeVolume n j i m *
      ‖envelopePairAverage n j i (fun y => localizedPair K L χ a (P i) (e y)) m‖ ^ 2 :=
    mul_nonneg (WeightMass.envelopeVolume_pos n j i m).le (sq_nonneg _)
  unfold familyEnergy
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => tsum_nonneg (hnn i))]
  apply Finset.sum_congr rfl
  intro i hi
  exact ENNReal.ofReal_tsum_of_nonneg (hnn i)
    (transported_pair_average_energy n j i e K L c hK hL hc χ hχ a ha (P i)).1

end
end CircleDivisor.EnergyV3.RefinedEnergy
