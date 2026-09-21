import CircleDivisor.EnergyV3.LocalizationNormalization
import CircleDivisor.EnergyV3.Statements
import CircleDivisor.UniformMoment

/-! The bounded-parameter case and the final normalization of the actual
first-spacing estimate. The localized estimate remains an internal premise
until instantiated by the envelope construction. -/
namespace CircleDivisor.EnergyV3.FirstSpacingTransfer
noncomputable section
open MeasureTheory
open scoped BigOperators

theorem momentBox_volume (K : ℝ) (hK : 0 ≤ K) :
    volume (momentBox K) = ENNReal.ofReal (2*Real.sqrt K) := by
  have he : momentBox K = Set.Icc
      (fun i : Fin 3 => if i=2 then -Real.sqrt K else 0)
      (fun i : Fin 3 => if i=2 then Real.sqrt K else 1) := by
    ext x
    simp only [momentBox, Set.mem_pi, Set.mem_univ, forall_const, Set.mem_Icc, Pi.le_def, ← forall_and]
    apply forall_congr'
    intro i
    split_ifs <;> rfl
  rw [he, Real.volume_Icc_pi]
  norm_num [Fin.prod_univ_succ, Fin.ext_iff, ← two_mul, ENNReal.ofReal_mul]

theorem coneMoment_zero (K L : ℝ) (hK : 0 < K) (a : ℤ → ℤ → ℂ) :
    coneMoment K L 0 a = 1 := by
  unfold coneMoment
  simp only [Real.rpow_zero, integral_const, smul_eq_mul, mul_one, Measure.real, Measure.restrict_apply_univ,
    momentBox_volume K hK.le, ENNReal.toReal_ofReal (by positivity : 0 ≤ 2*Real.sqrt K)]
  exact inv_mul_cancel₀ (by positivity : (2*Real.sqrt K:ℝ) ≠ 0)

theorem coneMoment_trivial (K L q : ℝ) (hL : 1 ≤ L) (hLK : L ≤ K) (hq : 0 ≤ q)
    (a : ℤ → ℤ → ℂ) (ha : ∀ k l, ‖a k l‖ ≤ 1) :
    coneMoment K L q a ≤ (4*(K*L))^q := by
  have hh := coneMoment_compare K L 0 q q hL hLK (by norm_num) hq (by linarith) a ha
  simpa only [coneMoment_zero K L (by linarith) a, mul_one] using hh

theorem fourTerm_one_le (K L q : ℝ) (hL : 1 ≤ L) (hLK : L ≤ K) (hq : 0 ≤ q) :
    1 ≤ Arithmetic.fourTerm K L q := by
  have hK : 1 ≤ K := hL.trans hLK
  have hP : 1 ≤ K*L := one_le_mul_of_one_le_of_one_le hK hL
  have hfirst := Real.one_le_rpow hP (show 0 ≤ q/2 by linarith)
  unfold Arithmetic.fourTerm
  have h1 : 0 ≤ K*L^(2*q-5) := by positivity
  have h2 : 0 ≤ K^(q-2)*L^(q-3) := by positivity
  have h3 : 0 ≤ K^(3*q/4-2)*L^(5*q/4-2) := by positivity
  linarith

theorem firstSpacing_of_large_localized
    (χ : SchwartzMap FourierLocalization.Space ℂ)
    (hχ : ∀ z : FourierLocalization.Space, ‖z‖ ≤ 3 → (1/2:ℝ) ≤ ‖χ z‖)
    (hlarge : ∀ q : ℝ, 4<q → q≤9/2 → ∀ ε : ℝ, 0<ε →
      ∃ P₀ C : ℝ, 1≤P₀ ∧ 0<C ∧ ∀ K L : ℝ, 1≤L → L≤K → P₀≤K*L →
        ∀ a : ℤ→ℤ→ℂ, (∀ k l, ‖a k l‖≤1) →
          (∫ z, ‖LocalizationNormalization.localized K L χ a z‖^q) ≤
            C*(K*L)^(3+ε)*Arithmetic.fourTerm K L q) :
    FirstSpacingStatement := by
  intro q hq hqu ε hε
  obtain ⟨P₀,C,hP₀,hC,hb⟩ := hlarge q hq hqu ε hε
  let C₀ : ℝ := (4*P₀)^q + 16*C
  have hC₀ : 0<C₀ := by dsimp [C₀]; positivity
  refine ⟨C₀,hC₀,?_⟩
  intro K L hL hLK a ha
  have hK : 1≤K := hL.trans hLK
  have hK0 : 0<K := by linarith
  have hL0 : 0<L := by linarith
  have hP : 1≤K*L := one_le_mul_of_one_le_of_one_le hK hL
  have hq0 : 0<q := by linarith
  have hB := fourTerm_one_le K L q hL hLK hq0.le
  have heps : 1≤(K*L)^ε := Real.one_le_rpow hP hε.le
  by_cases hbig : P₀≤K*L
  · have hh := LocalizationNormalization.coneMoment_le_localized_integral K L q hK hL0 hq0 hqu χ hχ a
    have hp : ((K*L)^3)⁻¹*(K*L)^(3+ε) = (K*L)^ε := by
      rw [Real.rpow_add (mul_pos hK0 hL0)]
      norm_num only [Real.rpow_natCast, Real.rpow_ofNat] 
      field_simp
    calc
      _ ≤ 16*((K*L)^3)⁻¹*(C*(K*L)^(3+ε)*Arithmetic.fourTerm K L q) :=
        hh.trans (mul_le_mul_of_nonneg_left (hb K L hL hLK hbig a ha) (by positivity))
      _ = 16*C*(K*L)^ε*Arithmetic.fourTerm K L q := by
        calc
          _ = 16*C*(((K*L)^3)⁻¹*(K*L)^(3+ε))*Arithmetic.fourTerm K L q := by ring
          _ = _ := by rw [hp]
      _ ≤ _ := by
        gcongr
        dsimp [C₀]
        exact le_add_of_nonneg_left (Real.rpow_nonneg (by positivity) _)
  · have hs : coneMoment K L q a ≤ (4*P₀)^q :=
      (coneMoment_trivial K L q hL hLK hq0.le a ha).trans
        (Real.rpow_le_rpow (by positivity) (by linarith) hq0.le)
    have hprod : 1 ≤ (K*L)^ε*Arithmetic.fourTerm K L q :=
      one_le_mul_of_one_le_of_one_le heps hB
    calc
      _ ≤ (4*P₀)^q := hs
      _ ≤ C₀ := by dsimp [C₀]; linarith
      _ ≤ C₀*((K*L)^ε*Arithmetic.fourTerm K L q) := le_mul_of_one_le_right hC₀.le hprod
      _ = _ := by ring

end
end CircleDivisor.EnergyV3.FirstSpacingTransfer
