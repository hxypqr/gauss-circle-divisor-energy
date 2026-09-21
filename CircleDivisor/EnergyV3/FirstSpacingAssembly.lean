import CircleDivisor.EnergyV3.AmplitudeScale

/-! Assembly of the actual GM distribution estimate and the two envelope
energies. This internal conditional lemma is instantiated with proved
actual density and energy estimates in `AnalyticAssembly.lean`. -/

namespace CircleDivisor.EnergyV3.FirstSpacingAssembly
noncomputable section
open MeasureTheory GuthMaldague AmplitudeCountable AmplitudeScale
open scoped BigOperators ENNReal

theorem moment_of_scale_data (K L C δ A E q : ℝ) (n : ℕ) (f : Space → ℂ)
    (hL : 1 ≤ L) (hLK : L ≤ K) (hR : radius n < 4 * (K * L))
    (hC : 0 ≤ C) (hA : 0 ≤ A) (hE : 0 ≤ E)
    (hf : AEMeasurable f volume) (hq : 4 < q) (hqu : q ≤ (9 : ℝ) / 2)
    (D : (j : ℕ) → (i : CapIndex j) → Lattice → ℝ)
    (hD : ∀ j ∈ Finset.Ioo 0 n, ∀ i m, 0 ≤ D j i m)
    (hd : ∀ j ∈ Finset.Ioo 0 n, ∀ i m,
      D j i m ≤ A * CircleDivisor.ScaleBounds.D K L (scale j))
    (hb : ∀ j ∈ Finset.Ioo 0 n, ∀ i m,
      |localMass n j i m f - D j i m| ≤ A * CircleDivisor.ScaleBounds.M K L (scale j))
    (hEd : ∀ j ∈ Finset.Ioo 0 n,
      sameEnergy n j (D j) ≤ ENNReal.ofReal (E * sameProfile K L (scale j)))
    (hEc : ∀ j ∈ Finset.Ioo 0 n,
      crossEnergy n j f (D j) ≤ ENNReal.ofReal (E * crossProfile K L (scale j)))
    (htail : ∀ α : ℝ, 0 < α → ENNReal.ofReal (α ^ (4 : ℕ)) * volume {x : Space | α < ‖f x‖} ≤
      ENNReal.ofReal (C * radius n ^ δ) * waveEnvelopeSum C δ α n f) :
    Integrable (fun x => ‖f x‖ ^ q) ∧
      (∫ x, ‖f x‖ ^ q) ≤
        128 * (C * radius n ^ δ) * E * (2 * (C * radius n ^ δ) * A) ^ ((q - 4) / 2) *
          (q / (q - 4)) * ((Finset.Ioo 0 n).card : ℝ) * Arithmetic.fourTerm K L q := by
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hK0 : 0 < K := hL0.trans_le hLK
  have hR0 := radius_pos n
  have hq0 : 0 < q := by linarith
  have hqd : 0 < q - 4 := by linarith
  obtain ⟨hi, hm⟩ := moment_of_gm C δ hC n f hf q hq D
    (fun j => A * CircleDivisor.ScaleBounds.D K L (scale j))
    (fun j => A * CircleDivisor.ScaleBounds.M K L (scale j))
    (fun j => E * sameProfile K L (scale j))
    (fun j => E * crossProfile K L (scale j)) hD hd hb hEd hEc
    (fun j _ => mul_nonneg hE (profile_nonneg hK0 hL0 (scale_pos j)).1)
    (fun j _ => mul_nonneg hE (profile_nonneg hK0 hL0 (scale_pos j)).2) htail
  refine ⟨hi, hm.trans ?_⟩
  have hh := mul_le_mul_of_nonneg_left
    (scale_sum hL hLK hR hq.le hqu (show 0 ≤ C * radius n ^ δ by positivity) hA hE)
    (show 0 ≤ 4 * (C * radius n ^ δ) * q / (q - 4) by positivity)
  convert hh using 1 <;> ring

def finalConstant (C A E q ε : ℝ) : ℝ :=
  256 * C ^ 2 * A * E * ((4 : ℝ) ^ (ε / 8)) ^ 2 *
    (1 / ((ε / 4) * Real.log 4) + 1) * (q / (q - 4))

theorem finalConstant_pos {C A E q ε : ℝ} (hC : 1 ≤ C) (hA : 1 ≤ A)
    (hE : 0 < E) (hq : 4 < q) (hε : 0 < ε) : 0 < finalConstant C A E q ε := by
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  unfold finalConstant
  positivity

theorem coefficient_bound {P C A E q ε : ℝ} {n : ℕ}
    (hP : 1 ≤ P) (hR : radius n < 4 * P)
    (hC : 1 ≤ C) (hA : 1 ≤ A) (hE : 0 ≤ E)
    (hq : 4 < q) (hqu : q ≤ (9 : ℝ) / 2) (hε : 0 < ε) :
    128 * (C * radius n ^ (ε / 8)) * (E * P ^ (3 + ε / 8)) *
      (2 * (C * radius n ^ (ε / 8)) * A) ^ ((q - 4) / 2) *
      (q / (q - 4)) * ((Finset.Ioo 0 n).card : ℝ) ≤
        finalConstant C A E q ε * P ^ (3 + ε) := by
  have hP0 : 0 < P := lt_of_lt_of_le zero_lt_one hP
  have hC0 : 0 ≤ C := by linarith
  have hA0 : 0 ≤ A := by linarith
  have hδ : 0 ≤ ε / 8 := by linarith
  have hR1 : 1 ≤ radius n := by exact one_le_pow₀ (by norm_num)
  have hB1 : 1 ≤ C * radius n ^ (ε / 8) :=
    one_le_mul_of_one_le_of_one_le hC (Real.one_le_rpow hR1 hδ)
  have hpow : (2 * (C * radius n ^ (ε / 8)) * A) ^ ((q - 4) / 2) ≤
      2 * (C * radius n ^ (ε / 8)) * A :=
    Real.rpow_le_self_of_one_le
      (one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le (by norm_num) hB1) hA) (by linarith)
  have hRpow : radius n ^ (ε / 8) ≤ (4 : ℝ) ^ (ε / 8) * P ^ (ε / 8) := by
    rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hP0.le]
    exact Real.rpow_le_rpow (radius_pos n).le hR.le hδ
  have hcount := scale_count hP hR (show 0 < ε / 4 by linarith)
  have hqdiv : 0 ≤ q / (q - 4) := by positivity
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hpower : P ^ (ε / 8) * P ^ (3 + ε / 8) * P ^ (ε / 8) * P ^ (ε / 4) =
      P ^ (3 + 5 * ε / 8) := by
    rw [← Real.rpow_add hP0, ← Real.rpow_add hP0, ← Real.rpow_add hP0]
    congr 1
    ring
  calc
    _ ≤ 128 * (C * radius n ^ (ε / 8)) * (E * P ^ (3 + ε / 8)) *
        (2 * (C * radius n ^ (ε / 8)) * A) * (q / (q - 4)) *
          ((Finset.Ioo 0 n).card : ℝ) := by gcongr
    _ ≤ 128 * (C * ((4 : ℝ) ^ (ε / 8) * P ^ (ε / 8))) * (E * P ^ (3 + ε / 8)) *
        (2 * (C * ((4 : ℝ) ^ (ε / 8) * P ^ (ε / 8))) * A) * (q / (q - 4)) *
          ((1 / ((ε / 4) * Real.log 4) + 1) * P ^ (ε / 4)) := by gcongr
    _ = finalConstant C A E q ε *
        (P ^ (ε / 8) * P ^ (3 + ε / 8) * P ^ (ε / 8) * P ^ (ε / 4)) := by
      unfold finalConstant
      ring
    _ ≤ finalConstant C A E q ε * P ^ (3 + ε) := by
      rw [hpower]
      apply mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hP (by linarith))
      unfold finalConstant
      positivity

/-- The final numerical implication for the real Schwartz moment. The losses
are `δ = γ = ε/8` and the scale-count loss is `ε/4`. We use the harmless
coarser bound `x^((q-4)/2) ≤ x`, so the total loss is `5ε/8 < ε`.
The factor `q/(q-4)` remains explicit in `finalConstant`. -/
theorem moment_bound (K L C A E q ε : ℝ) (n : ℕ) (f : Space → ℂ)
    (hL : 1 ≤ L) (hLK : L ≤ K) (hR : radius n < 4 * (K * L))
    (hC : 1 ≤ C) (hA : 1 ≤ A) (hE : 0 < E) (hε : 0 < ε)
    (hf : AEMeasurable f volume) (hq : 4 < q) (hqu : q ≤ (9 : ℝ) / 2)
    (D : (j : ℕ) → (i : CapIndex j) → Lattice → ℝ)
    (hD : ∀ j ∈ Finset.Ioo 0 n, ∀ i m, 0 ≤ D j i m)
    (hd : ∀ j ∈ Finset.Ioo 0 n, ∀ i m,
      D j i m ≤ A * CircleDivisor.ScaleBounds.D K L (scale j))
    (hb : ∀ j ∈ Finset.Ioo 0 n, ∀ i m,
      |localMass n j i m f - D j i m| ≤ A * CircleDivisor.ScaleBounds.M K L (scale j))
    (hEd : ∀ j ∈ Finset.Ioo 0 n,
      sameEnergy n j (D j) ≤ ENNReal.ofReal
        ((E * (K * L) ^ (3 + ε / 8)) * sameProfile K L (scale j)))
    (hEc : ∀ j ∈ Finset.Ioo 0 n,
      crossEnergy n j f (D j) ≤ ENNReal.ofReal
        ((E * (K * L) ^ (3 + ε / 8)) * crossProfile K L (scale j)))
    (htail : ∀ α : ℝ, 0 < α → ENNReal.ofReal (α ^ (4 : ℕ)) * volume {x : Space | α < ‖f x‖} ≤
      ENNReal.ofReal (C * radius n ^ (ε / 8)) * waveEnvelopeSum C (ε / 8) α n f) :
    Integrable (fun x => ‖f x‖ ^ q) ∧
      (∫ x, ‖f x‖ ^ q) ≤
        finalConstant C A E q ε * (K * L) ^ (3 + ε) * Arithmetic.fourTerm K L q := by
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hK0 : 0 < K := hL0.trans_le hLK
  have hP : 1 ≤ K * L := one_le_mul_of_one_le_of_one_le (hL.trans hLK) hL
  obtain ⟨hi, hm⟩ := moment_of_scale_data K L C (ε / 8) A (E * (K * L) ^ (3 + ε / 8)) q n f
    hL hLK hR (by linarith) (by linarith) (by positivity) hf hq hqu D hD hd hb hEd hEc htail
  refine ⟨hi, hm.trans ?_⟩
  exact mul_le_mul_of_nonneg_right (coefficient_bound hP hR hC hA hE.le hq hqu hε)
    (by unfold Arithmetic.fourTerm; positivity)

end
end CircleDivisor.EnergyV3.FirstSpacingAssembly
