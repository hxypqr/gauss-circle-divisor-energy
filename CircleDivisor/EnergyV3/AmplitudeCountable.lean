import CircleDivisor.Energy
import CircleDivisor.AmplitudeIntegration
import CircleDivisor.EnergyV3.WeightMass
import CircleDivisor.EnergyV3.ScaleBounds

/-! Countable signed amplitude splitting. All infinite sums in this file are
nonnegative ENNReal sums, so no convergence is assumed to exchange them. -/

namespace CircleDivisor.EnergyV3.AmplitudeCountable
noncomputable section
open MeasureTheory GuthMaldague
open scoped ENNReal BigOperators

def cutoff (B d s : ℝ) : ℝ := Real.sqrt (2 * B * d) / s

theorem cutoff_nonneg {B d s : ℝ} (hs : 0 ≤ s) : 0 ≤ cutoff B d s := by
  exact div_nonneg (Real.sqrt_nonneg _) hs

theorem cutoff_of_square {α B d s : ℝ} (hα : 0 ≤ α) (hB : 0 ≤ B) (hd : 0 ≤ d)
    (hs : 0 < s) (h : α ^ 2 * s ^ 2 ≤ 2 * B * d) : α ≤ cutoff B d s := by
  apply (le_div_iff₀ hs).mpr
  have hr := Real.sq_sqrt (show 0 ≤ 2 * B * d by positivity)
  nlinarith [Real.sqrt_nonneg (2 * B * d), mul_nonneg hα hs.le]

theorem pointwise_split {w M D C d b α B s : ℝ}
    (hw : 0 ≤ w) (hM : 0 ≤ M) (hD : 0 ≤ D) (h : M = D + C)
    (hd : D ≤ d) (hb : |C| ≤ b) (hα : 0 ≤ α) (hB : 0 ≤ B) (hs : 0 < s) :
    (if α ^ 2 * s ^ 2 ≤ B * M then w * M ^ 2 else 0) ≤
      4 * ((if α ≤ cutoff B d s then w * D ^ 2 else 0) +
        (if α ≤ cutoff B b s then w * C ^ 2 else 0)) := by
  have hdn : 0 ≤ d := hD.trans hd
  have hbn : 0 ≤ b := (abs_nonneg _).trans hb
  by_cases hg : α ^ 2 * s ^ 2 ≤ B * M
  · rw [if_pos hg]
    have hsum : M ≤ D + |C| := by rw [h]; linarith [le_abs_self C]
    have hhalf : M / 2 ≤ D ∨ M / 2 ≤ |C| := by by_contra! hn; linarith
    rcases hhalf with hhalf | hhalf
    · have hcut : α ≤ cutoff B d s := cutoff_of_square hα hB hdn hs
        (hg.trans (by nlinarith [mul_nonneg hB (show 0 ≤ 2 * d - M by linarith)]))
      rw [if_pos hcut]
      have hsq : M ^ 2 ≤ 4 * D ^ 2 := by nlinarith
      have := mul_le_mul_of_nonneg_left hsq hw
      split_ifs <;> nlinarith [mul_nonneg hw (sq_nonneg C)]
    · have hcut : α ≤ cutoff B b s := cutoff_of_square hα hB hbn hs
        (hg.trans (by nlinarith [mul_nonneg hB (show 0 ≤ 2 * b - M by linarith)]))
      rw [if_pos hcut]
      have hsq : M ^ 2 ≤ 4 * C ^ 2 := by nlinarith [sq_abs C, abs_nonneg C]
      have := mul_le_mul_of_nonneg_left hsq hw
      split_ifs <;> nlinarith [mul_nonneg hw (sq_nonneg D)]
  · rw [if_neg hg]
    split_ifs <;> positivity

theorem countable_split {ι : Type*} (w M D C : ι → ℝ) (d b α B s : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hM : ∀ i, 0 ≤ M i) (hD : ∀ i, 0 ≤ D i)
    (h : ∀ i, M i = D i + C i) (hd : ∀ i, D i ≤ d) (hb : ∀ i, |C i| ≤ b)
    (hα : 0 ≤ α) (hB : 0 ≤ B) (hs : 0 < s) :
    (∑' i, if α ^ 2 * s ^ 2 ≤ B * M i then ENNReal.ofReal (w i * M i ^ 2) else 0) ≤
      4 * ((if α ≤ cutoff B d s then ∑' i, ENNReal.ofReal (w i * D i ^ 2) else 0) +
        (if α ≤ cutoff B b s then ∑' i, ENNReal.ofReal (w i * C i ^ 2) else 0)) := by
  classical
  have hp (i : ι) := ENNReal.ofReal_le_ofReal
    (pointwise_split (hw i) (hM i) (hD i) (h i) (hd i) (hb i) hα hB hs)
  have hp' (i : ι) :
      (if α ^ 2 * s ^ 2 ≤ B * M i then ENNReal.ofReal (w i * M i ^ 2) else 0) ≤
        4 * ((if α ≤ cutoff B d s then ENNReal.ofReal (w i * D i ^ 2) else 0) +
          (if α ≤ cutoff B b s then ENNReal.ofReal (w i * C i ^ 2) else 0)) := by
    have hp := hp i
    split_ifs at hp ⊢ <;>
      simp only [ENNReal.ofReal_zero, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4),
        ENNReal.ofReal_add (mul_nonneg (hw i) (sq_nonneg _))
          (mul_nonneg (hw i) (sq_nonneg _)), ENNReal.ofReal_ofNat, add_zero, zero_add] at hp ⊢ <;>
      exact hp
  calc
    _ ≤ ∑' i, 4 * ((if α ≤ cutoff B d s then ENNReal.ofReal (w i * D i ^ 2) else 0) +
        (if α ≤ cutoff B b s then ENNReal.ofReal (w i * C i ^ 2) else 0)) := ENNReal.tsum_le_tsum hp'
    _ = _ := by
      rw [ENNReal.tsum_mul_left, ENNReal.tsum_add]
      split_ifs <;> simp

theorem gm_envelope_split (C ε α : ℝ) (hC : 0 ≤ C) (hα : 0 ≤ α)
    (n j : ℕ) (i : CapIndex j) (f : Space → ℂ)
    (D : Lattice → ℝ) (d b : ℝ) (hD : ∀ m, 0 ≤ D m)
    (hd : ∀ m, D m ≤ d) (hb : ∀ m, |localMass n j i m f - D m| ≤ b) :
    envelopeEnergy C ε α n j i f ≤
      4 * ((if α ≤ cutoff (C * radius n ^ ε) d (scale j) then
          ∑' m : Lattice, ENNReal.ofReal (envelopeVolume n j i m * D m ^ 2) else 0) +
        (if α ≤ cutoff (C * radius n ^ ε) b (scale j) then
          ∑' m : Lattice, ENNReal.ofReal (envelopeVolume n j i m *
            (localMass n j i m f - D m) ^ 2) else 0)) := by
  classical
  apply le_trans (b := ∑' m : Lattice, if α ^ 2 * scale j ^ 2 ≤
    (C * radius n ^ ε) * localMass n j i m f then
      ENNReal.ofReal (envelopeVolume n j i m * localMass n j i m f ^ 2) else 0)
  · apply ENNReal.tsum_le_tsum
    intro m
    by_cases hg : contributing C ε α n j i m f
    · have ht := contributing_mass_threshold C ε α hC n j i m f hg
      simp [hg, ht]
    · simp [hg]
  · exact countable_split (envelopeVolume n j i) (fun m => localMass n j i m f) D
      (fun m => localMass n j i m f - D m) d b α (C * radius n ^ ε) (scale j)
      (fun m => (WeightMass.envelopeVolume_pos n j i m).le) (fun m => localMass_nonneg n j i m f)
      hD (fun _ => by ring) hd hb hα (mul_nonneg hC (Real.rpow_nonneg (radius_pos n).le _))
      (scale_pos j)

def sameEnergy (n j : ℕ) (D : (i : CapIndex j) → Lattice → ℝ) : ℝ≥0∞ :=
  ∑ i : CapIndex j, ∑' m : Lattice, ENNReal.ofReal (envelopeVolume n j i m * D i m ^ 2)

def crossEnergy (n j : ℕ) (f : Space → ℂ) (D : (i : CapIndex j) → Lattice → ℝ) : ℝ≥0∞ :=
  ∑ i : CapIndex j, ∑' m : Lattice,
    ENNReal.ofReal (envelopeVolume n j i m * (localMass n j i m f - D i m) ^ 2)

theorem gm_scale_split (C ε α : ℝ) (hC : 0 ≤ C) (hα : 0 ≤ α)
    (n j : ℕ) (f : Space → ℂ) (D : (i : CapIndex j) → Lattice → ℝ) (d b : ℝ)
    (hD : ∀ i m, 0 ≤ D i m) (hd : ∀ i m, D i m ≤ d)
    (hb : ∀ i m, |localMass n j i m f - D i m| ≤ b) :
    (∑ i : CapIndex j, envelopeEnergy C ε α n j i f) ≤
      4 * ((if α ≤ cutoff (C * radius n ^ ε) d (scale j) then sameEnergy n j D else 0) +
        (if α ≤ cutoff (C * radius n ^ ε) b (scale j) then crossEnergy n j f D else 0)) := by
  classical
  apply (Finset.sum_le_sum (fun i _ => gm_envelope_split C ε α hC hα n j i f (D i)
    d b (hD i) (hd i) (hb i))).trans_eq
  unfold sameEnergy crossEnergy
  split_ifs <;> simp [Finset.mul_sum, Finset.sum_add_distrib, mul_add]

theorem gm_truncated_distribution (C ε : ℝ) (hC : 0 ≤ C) (n : ℕ) (f : Space → ℂ)
    (D : (j : ℕ) → (i : CapIndex j) → Lattice → ℝ) (d b Ed Ec : ℕ → ℝ)
    (hD : ∀ j ∈ Finset.Ioo 0 n, ∀ i m, 0 ≤ D j i m)
    (hd : ∀ j ∈ Finset.Ioo 0 n, ∀ i m, D j i m ≤ d j)
    (hb : ∀ j ∈ Finset.Ioo 0 n, ∀ i m, |localMass n j i m f - D j i m| ≤ b j)
    (hEd : ∀ j ∈ Finset.Ioo 0 n, sameEnergy n j (D j) ≤ ENNReal.ofReal (Ed j))
    (hEc : ∀ j ∈ Finset.Ioo 0 n, crossEnergy n j f (D j) ≤ ENNReal.ofReal (Ec j))
    (htail : ∀ α : ℝ, 0 < α → ENNReal.ofReal (α ^ (4 : ℕ)) * volume {x : Space | α < ‖f x‖} ≤
      ENNReal.ofReal (C * radius n ^ ε) * waveEnvelopeSum C ε α n f) :
    ∀ α : ℝ, 0 < α → ENNReal.ofReal (α ^ (4 : ℕ)) * volume {x : Space | α < ‖f x‖} ≤
      ENNReal.ofReal (4 * (C * radius n ^ ε)) * ∑ j ∈ Finset.Ioo 0 n,
        ((if α ≤ cutoff (C * radius n ^ ε) (d j) (scale j) then ENNReal.ofReal (Ed j) else 0) +
         (if α ≤ cutoff (C * radius n ^ ε) (b j) (scale j) then ENNReal.ofReal (Ec j) else 0)) := by
  classical
  intro α hα
  have hs : waveEnvelopeSum C ε α n f ≤ 4 * ∑ j ∈ Finset.Ioo 0 n,
        ((if α ≤ cutoff (C * radius n ^ ε) (d j) (scale j) then ENNReal.ofReal (Ed j) else 0) +
         (if α ≤ cutoff (C * radius n ^ ε) (b j) (scale j) then ENNReal.ofReal (Ec j) else 0)) := by
    unfold waveEnvelopeSum
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    apply (gm_scale_split C ε α hC hα.le n j f (D j) (d j) (b j) (hD j hj) (hd j hj) (hb j hj)).trans
    gcongr
    · split_ifs <;> first | exact hEd j hj | exact le_rfl
    · split_ifs <;> first | exact hEc j hj | exact le_rfl
  apply (htail α hα).trans
  calc
    _ ≤ ENNReal.ofReal (C * radius n ^ ε) * (4 * ∑ j ∈ Finset.Ioo 0 n,
        ((if α ≤ cutoff (C * radius n ^ ε) (d j) (scale j) then ENNReal.ofReal (Ed j) else 0) +
         (if α ≤ cutoff (C * radius n ^ ε) (b j) (scale j) then ENNReal.ofReal (Ec j) else 0))) :=
      mul_le_mul_left' hs _
    _ = _ := by rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4), ENNReal.ofReal_ofNat]; ring

theorem moment_of_gm (C ε : ℝ) (hC : 0 ≤ C) (n : ℕ) (f : Space → ℂ)
    (hf : AEMeasurable f volume) (q : ℝ) (hq : 4 < q)
    (D : (j : ℕ) → (i : CapIndex j) → Lattice → ℝ) (d b Ed Ec : ℕ → ℝ)
    (hD : ∀ j ∈ Finset.Ioo 0 n, ∀ i m, 0 ≤ D j i m)
    (hd : ∀ j ∈ Finset.Ioo 0 n, ∀ i m, D j i m ≤ d j)
    (hb : ∀ j ∈ Finset.Ioo 0 n, ∀ i m, |localMass n j i m f - D j i m| ≤ b j)
    (hEd : ∀ j ∈ Finset.Ioo 0 n, sameEnergy n j (D j) ≤ ENNReal.ofReal (Ed j))
    (hEc : ∀ j ∈ Finset.Ioo 0 n, crossEnergy n j f (D j) ≤ ENNReal.ofReal (Ec j))
    (hEd0 : ∀ j ∈ Finset.Ioo 0 n, 0 ≤ Ed j) (hEc0 : ∀ j ∈ Finset.Ioo 0 n, 0 ≤ Ec j)
    (htail : ∀ α : ℝ, 0 < α → ENNReal.ofReal (α ^ (4 : ℕ)) * volume {x : Space | α < ‖f x‖} ≤
      ENNReal.ofReal (C * radius n ^ ε) * waveEnvelopeSum C ε α n f) :
    Integrable (fun x => ‖f x‖ ^ q) ∧
      (∫ x, ‖f x‖ ^ q) ≤ 4 * (C * radius n ^ ε) * q / (q - 4) *
        ∑ j ∈ Finset.Ioo 0 n,
          (Ed j * cutoff (C * radius n ^ ε) (d j) (scale j) ^ (q - 4) +
           Ec j * cutoff (C * radius n ^ ε) (b j) (scale j) ^ (q - 4)) := by
  exact AmplitudeIntegration.integral_norm_moment_two_cutoffs volume (Finset.Ioo 0 n) f hf q hq
    (4 * (C * radius n ^ ε))
    (mul_nonneg (by norm_num) (mul_nonneg hC (Real.rpow_nonneg (radius_pos n).le _))) Ed Ec
    (fun j => cutoff (C * radius n ^ ε) (d j) (scale j))
    (fun j => cutoff (C * radius n ^ ε) (b j) (scale j)) hEd0 hEc0
    (fun j _ => cutoff_nonneg (scale_pos j).le) (fun j _ => cutoff_nonneg (scale_pos j).le)
    (gm_truncated_distribution C ε hC n f D d b Ed Ec hD hd hb hEd hEc htail)

end
end CircleDivisor.EnergyV3.AmplitudeCountable
