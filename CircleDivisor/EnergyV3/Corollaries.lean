import CircleDivisor.EnergyV3.FirstSpacingProof

/-! The square-root corollary for the actual normalized cone moment, including
the explicit uniform endpoint loss and the revised `K ≤ L³` endpoint range. -/
namespace CircleDivisor.EnergyV3.Corollaries
noncomputable section

theorem sqrt_moment_of_uniform (hfirst : UniformFirstSpacingStatement) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ q : ℝ, 4 < q → q ≤ 9/2 → ∀ K L : ℝ, 1 ≤ L → L ≤ K →
      K^(q-4) ≤ L^(6-q) → L^(3*q-8) ≤ K^(8-q) →
      ∀ a : ℤ → ℤ → ℂ, (∀ k l, ‖a k l‖ ≤ 1) →
        coneMoment K L q a ≤ C*(q/(q-4))*(K*L)^(q/2+ε) := by
  intro ε hε
  obtain ⟨C,hC,hb⟩ := hfirst ε hε
  refine ⟨4*C,by positivity,?_⟩
  intro q hq hqu K L hL hLK hf hs a ha
  have hL0 : 0 < L := by linarith
  have hK0 : 0 < K := by linarith
  have hP : 0 < K*L := mul_pos hK0 hL0
  have hfac : 0 < q/(q-4) := div_pos (by linarith) (by linarith)
  have hfour := Arithmetic.fourTerm_le hL hLK hq hqu hf hs
  calc
    _ ≤ C*(q/(q-4))*(K*L)^ε*Arithmetic.fourTerm K L q := hb q hq hqu K L hL hLK a ha
    _ ≤ C*(q/(q-4))*(K*L)^ε*(4*(K*L)^(q/2)) :=
      mul_le_mul_of_nonneg_left hfour (by positivity)
    _ = (4*C)*(q/(q-4))*((K*L)^ε*(K*L)^(q/2)) := by ring
    _ = _ := by rw [← Real.rpow_add hP, add_comm ε (q/2)]

/-- Corollary `cor:sqrt`, using only the external inputs already needed for
the first-spacing theorem. The constant is uniform in `4 < q ≤ 9/2`. -/
theorem sqrt_moment_of_external_inputs
    (hGM : GuthMaldague.GuthMaldagueInput) (hdiv : ClassicalInputs.DivisorBound) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ q : ℝ, 4 < q → q ≤ 9/2 → ∀ K L : ℝ, 1 ≤ L → L ≤ K →
      K^(q-4) ≤ L^(6-q) → L^(3*q-8) ≤ K^(8-q) →
      ∀ a : ℤ → ℤ → ℂ, (∀ k l, ‖a k l‖ ≤ 1) →
        coneMoment K L q a ≤ C*(q/(q-4))*(K*L)^(q/2+ε) :=
  sqrt_moment_of_uniform (uniformFirstSpacing_of_external_inputs hGM hdiv)

theorem nine_halves_conditions {K L : ℝ} (hL : 1 ≤ L)
    (hlower : L^((11:ℝ)/7) ≤ K) (hupper : K ≤ L^3) :
    L ≤ K ∧ K^((9:ℝ)/2-4) ≤ L^(6-(9:ℝ)/2) ∧
      L^(3*((9:ℝ)/2)-8) ≤ K^(8-(9:ℝ)/2) := by
  have hL0 : 0 < L := by linarith
  have hLK : L ≤ K := by
    calc
      L = L^(1:ℝ) := (Real.rpow_one L).symm
      _ ≤ L^((11:ℝ)/7) := Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
      _ ≤ K := hlower
  have hK0 : 0 < K := by linarith
  have hlo := (Real.log_le_log_iff (Real.rpow_pos_of_pos hL0 ((11:ℝ)/7)) hK0).mpr hlower
  have hhi := (Real.log_le_log_iff hK0 (pow_pos hL0 3)).mpr hupper
  rw [Real.log_rpow hL0] at hlo
  rw [Real.log_pow] at hhi
  norm_num only [Nat.cast_ofNat] at hhi
  refine ⟨hLK,?_,?_⟩
  · apply (Real.log_le_log_iff (Real.rpow_pos_of_pos hK0 _) (Real.rpow_pos_of_pos hL0 _)).mp
    rw [Real.log_rpow hK0, Real.log_rpow hL0]
    linarith
  · apply (Real.log_le_log_iff (Real.rpow_pos_of_pos hL0 _) (Real.rpow_pos_of_pos hK0 _)).mp
    rw [Real.log_rpow hL0, Real.log_rpow hK0]
    linarith

/-- The endpoint range in the revised manuscript is `L^(11/7) ≤ K ≤ L³`. -/
theorem nine_halves_moment_of_external_inputs
    (hGM : GuthMaldague.GuthMaldagueInput) (hdiv : ClassicalInputs.DivisorBound) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ K L : ℝ, 1 ≤ L →
      L^((11:ℝ)/7) ≤ K → K ≤ L^3 →
      ∀ a : ℤ → ℤ → ℂ, (∀ k l, ‖a k l‖ ≤ 1) →
        coneMoment K L (9/2) a ≤ C*(K*L)^(9/4+ε) := by
  intro ε hε
  obtain ⟨C,hC,hb⟩ := sqrt_moment_of_external_inputs hGM hdiv ε hε
  refine ⟨9*C,by positivity,?_⟩
  intro K L hL hlo hhi a ha
  obtain ⟨hLK,hf,hs⟩ := nine_halves_conditions hL hlo hhi
  have hh := hb (9/2) (by norm_num) le_rfl K L hL hLK hf hs a ha
  norm_num only [show (9:ℝ)/2/((9:ℝ)/2-4)=9 by norm_num,
    show (9:ℝ)/2/2=9/4 by norm_num] at hh
  calc
    _ ≤ C*9*(K*L)^(9/4+ε) := hh
    _ = _ := by ring

end
end CircleDivisor.EnergyV3.Corollaries
