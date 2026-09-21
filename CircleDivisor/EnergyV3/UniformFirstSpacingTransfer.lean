import CircleDivisor.EnergyV3.FirstSpacingTransfer

/-! Uniform normalization of the first-spacing estimate. The bounded product
range uses one fifth-power constant for every `4 < q ≤ 9/2`; the large-product
range retains exactly the displayed `q/(q-4)` loss. -/
namespace CircleDivisor.EnergyV3.UniformFirstSpacingTransfer
noncomputable section
open MeasureTheory FirstSpacingTransfer

theorem uniformFirstSpacing_of_large_localized
    (χ : SchwartzMap FourierLocalization.Space ℂ)
    (hχ : ∀ z : FourierLocalization.Space, ‖z‖ ≤ 3 → (1/2:ℝ) ≤ ‖χ z‖)
    (hlarge : ∀ ε : ℝ, 0 < ε → ∃ P₀ C : ℝ, 1 ≤ P₀ ∧ 0 < C ∧
      ∀ q : ℝ, 4 < q → q ≤ 9/2 → ∀ K L : ℝ, 1 ≤ L → L ≤ K → P₀ ≤ K*L →
        ∀ a : ℤ → ℤ → ℂ, (∀ k l, ‖a k l‖ ≤ 1) →
          (∫ z, ‖LocalizationNormalization.localized K L χ a z‖^q) ≤
            C*(q/(q-4))*(K*L)^(3+ε)*Arithmetic.fourTerm K L q) :
    UniformFirstSpacingStatement := by
  intro ε hε
  obtain ⟨P₀,C,hP₀,hC,hb⟩ := hlarge ε hε
  let C₀ : ℝ := (4*P₀)^5 + 16*C
  have hC₀ : 0 < C₀ := by dsimp [C₀]; positivity
  refine ⟨C₀,hC₀,?_⟩
  intro q hq hqu K L hL hLK a ha
  have hK : 1 ≤ K := hL.trans hLK
  have hK0 : 0 < K := by linarith
  have hL0 : 0 < L := by linarith
  have hP : 1 ≤ K*L := one_le_mul_of_one_le_of_one_le hK hL
  have hq0 : 0 < q := by linarith
  have hfactor : 1 ≤ q/(q-4) := (one_le_div (by linarith : 0 < q-4)).mpr (by linarith)
  have hfactor0 : 0 < q/(q-4) := by linarith
  have hB := fourTerm_one_le K L q hL hLK hq0.le
  have heps : 1 ≤ (K*L)^ε := Real.one_le_rpow hP hε.le
  by_cases hbig : P₀ ≤ K*L
  · have hh := LocalizationNormalization.coneMoment_le_localized_integral K L q
      hK hL0 hq0 hqu χ hχ a
    have hp : ((K*L)^3)⁻¹*(K*L)^(3+ε) = (K*L)^ε := by
      rw [Real.rpow_add (mul_pos hK0 hL0)]
      norm_num only [Real.rpow_natCast, Real.rpow_ofNat]
      field_simp
    calc
      _ ≤ 16*((K*L)^3)⁻¹*(C*(q/(q-4))*(K*L)^(3+ε)*Arithmetic.fourTerm K L q) :=
        hh.trans (mul_le_mul_of_nonneg_left (hb q hq hqu K L hL hLK hbig a ha) (by positivity))
      _ = 16*C*(q/(q-4))*(K*L)^ε*Arithmetic.fourTerm K L q := by
        calc
          _ = 16*C*(q/(q-4))*(((K*L)^3)⁻¹*(K*L)^(3+ε))*Arithmetic.fourTerm K L q := by ring
          _ = _ := by rw [hp]
      _ ≤ _ := by
        gcongr
        dsimp [C₀]
        have hp5 : 0 ≤ (4*P₀)^5 := by positivity
        linarith
  · have hs : coneMoment K L q a ≤ (4*P₀)^q :=
      (coneMoment_trivial K L q hL hLK hq0.le a ha).trans
        (Real.rpow_le_rpow (by positivity) (by linarith) hq0.le)
    have hq5 : (4*P₀)^q ≤ (4*P₀)^5 := by
      calc
        _ ≤ (4*P₀)^(5:ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
        _ = _ := Real.rpow_ofNat _ 5
    have hprod : 1 ≤ (q/(q-4))*(K*L)^ε*Arithmetic.fourTerm K L q :=
      one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le hfactor heps) hB
    calc
      _ ≤ (4*P₀)^5 := hs.trans hq5
      _ ≤ C₀ := by dsimp [C₀]; linarith
      _ ≤ C₀*((q/(q-4))*(K*L)^ε*Arithmetic.fourTerm K L q) :=
        le_mul_of_one_le_right hC₀.le hprod
      _ = _ := by ring

end
end CircleDivisor.EnergyV3.UniformFirstSpacingTransfer
