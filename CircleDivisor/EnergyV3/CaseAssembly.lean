import CircleDivisor.EnergyV3.Construction

/-! Actual positive real parameters for the internal Case A/B selection.
The logarithmic coordinates are evaluated, and the displayed block lengths
are proved equal to the selected real powers. -/

namespace CircleDivisor.EnergyV3.CaseAssembly
noncomputable section
open CircleDivisor.Arithmetic CircleDivisor.ExternalInterfaces
open CircleDivisor.LogScale

def SixMargins (h m n : ℝ) : Prop :=
  1 / 1000 ≤ radiusExponent m n ∧
  1 / 1000 ≤ h - radiusExponent m n ∧
  1 / 1000 ≤ n - h ∧ 1 / 1000 ≤ m - n ∧
  1 / 1000 ≤ 2 * radiusExponent m n - h ∧
  1 / 1000 ≤ m + 2 * radiusExponent m n - h - 2 * n

theorem exponent_rpow (T x : ℝ) (hT : 1 < T) : exponent T (T^x) = x := by
  unfold exponent
  rw [Real.log_rpow (by linarith)]
  have hl : Real.log T ≠ 0 := ne_of_gt (Real.log_pos hT)
  field_simp

theorem blockLengthA_power (T h m : ℝ) (hT : 1 < T) :
    blockLengthA (T^h) (T^m) T =
      T^blockA h m (exponent T (Real.log T)) := by
  have ht : 0 < T := by linarith
  rw [blockLengthA_eq_power T (T^h) (T^m) hT (by positivity) (by positivity),
    exponent_rpow T h hT, exponent_rpow T m hT]

theorem blockLengthB_power (T h m : ℝ) (hT : 1 < T) :
    blockLengthB (T^h) (T^m) T =
      T^min (blockB₁ h m (exponent T (Real.log T))) (blockB₂ h m) := by
  have ht : 0 < T := by linarith
  rw [blockLengthB_eq_power T (T^h) (T^m) hT (by positivity) (by positivity),
    exponent_rpow T h hT, exponent_rpow T m hT]

theorem caseBoundary_power (T m : ℝ) (hT : 1 < T) :
    (T^m)^(-9:ℝ)*T^(4:ℝ)*(Real.log T)^((171:ℝ)/140) =
      T^caseBoundary m (exponent T (Real.log T)) := by
  have ht : 0 < T := by linarith
  nth_rewrite 1 [← rpow_exponent T (Real.log T) hT (Real.log_pos hT)]
  simp only [← Real.rpow_mul ht.le, ← Real.rpow_add ht]
  congr 1
  unfold caseBoundary
  ring

theorem selected_case (B₀ T h m : ℝ) (hB : 0 < B₀) (hT : 1 < T)
    (hr : HardRange theta h m)
    (he0 : 0 ≤ exponent T (Real.log T)) (he1 : exponent T (Real.log T) ≤ 1/1000)
    (hlargeB : 1/B₀ ≤ T^((137:ℝ)/7312)) :
    ∃ b : BlockCase, ∃ n : ℝ,
      admissibleCase b B₀ (T^h) (T^m) T ∧
      blockLength b (T^h) (T^m) T = T^n ∧
      blockA h m (exponent T (Real.log T)) ≤ n ∧ SixMargins h m n := by
  have ht : 0 < T := by linarith
  rcases Arithmetic.arithmetic_cases_cover hr he1 with hA | hBcase
  · refine ⟨.A, blockA h m (exponent T (Real.log T)), ?_, ?_, le_rfl, ?_⟩
    · change caseA (T^h) (T^m) T
      constructor
      · rw [caseBoundary_power T m hT]
        exact Real.rpow_le_rpow_of_exponent_le hT.le hA.1
      · rw [← Real.rpow_add ht]
        apply Real.rpow_le_rpow_of_exponent_le hT.le
        linarith [hA.2]
    · exact blockLengthA_power T h m hT
    · exact Arithmetic.caseA_six_margins hr he0 he1
  · let n := min (blockB₁ h m (exponent T (Real.log T))) (blockB₂ h m)
    refine ⟨.B,n,?_,?_,hBcase.2.2.2,?_⟩
    · change caseB B₀ (T^h) (T^m) T
      apply le_min
      · rw [← Real.rpow_mul ht.le, ← Real.rpow_add ht]
        exact Real.rpow_le_rpow_of_exponent_le hT.le (by linarith [hBcase.2.1])
      · have hf := CircleDivisor.BlockSeparation.factor_rpow_le T (137/7312) h
          (3*m/2-1/2) (1/B₀) hT.le (by linarith [hBcase.2.2.1]) hlargeB
        have hf' : T^h ≤ B₀*T^(3*m/2-1/2) := by
          have hf'' : T^h/B₀ ≤ T^(3*m/2-1/2) := by simpa [div_eq_mul_inv, mul_comm] using hf
          have hh := (div_le_iff₀ hB).mp hf''
          nlinarith
        have hid : B₀*(T^m)^((3:ℝ)/2)*T^(-(1:ℝ)/2) = B₀*T^(3*m/2-1/2) := by
          rw [← Real.rpow_mul ht.le, mul_assoc, ← Real.rpow_add ht]
          congr 2
          ring
        rwa [hid]
    · exact blockLengthB_power T h m hT
    · exact Arithmetic.caseB_six_margins hr he0 he1 hBcase.1.le
        hBcase.2.2.2 (min_le_right _ _)

/-- The common logarithmic threshold, with the tighter correction required
for all six revised construction margins. -/
theorem eventually_log_correction :
    ∀ᶠ T : ℝ in Filter.atTop,
      0 ≤ exponent T (Real.log T) ∧ exponent T (Real.log T) ≤ 1/1000 := by
  have hu := log_correction_tendsto.eventually
    (gt_mem_nhds (by norm_num : (0:ℝ)<1/1000))
  have hl := Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop (1:ℝ))
  filter_upwards [hu,hl] with T hU hL
  exact ⟨div_nonneg (Real.log_nonneg hL) (by linarith), hU.le⟩

end
end CircleDivisor.EnergyV3.CaseAssembly
