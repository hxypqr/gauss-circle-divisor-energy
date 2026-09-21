import CircleDivisor.EnergyV3.Optimization
import CircleDivisor.Arithmetic
import CircleDivisor.FirstSpacingConsequences
import CircleDivisor.LogScale

/-! Internal arithmetic for the revised four-term energy bound. In particular,
the third monomial here is `K^(q-2) L^(q-3)`, not the older manuscript's term.
The scale conclusions below verify six construction inequalities, including
the two inequalities that were not included in the previous formalization. -/

namespace CircleDivisor.EnergyV3.Arithmetic
noncomputable section
open CircleDivisor.Arithmetic

def fourTerm (K L q : ℝ) : ℝ :=
  (K * L) ^ (q / 2) + K * L ^ (2 * q - 5) +
    K ^ (q - 2) * L ^ (q - 3) +
    K ^ (3 * q / 4 - 2) * L ^ (5 * q / 4 - 2)

theorem denominator_powers (q : ℝ) :
    denominatorPower q (q / 2) (q / 2) = 8 - 2 * q ∧
    denominatorPower q 1 (2 * q - 5) = 4 - q ∧
    denominatorPower q (q - 2) (q - 3) = 3 - q ∧
    denominatorPower q (3 * q / 4 - 2) (5 * q / 4 - 2) = 4 - q := by
  dsimp [denominatorPower]
  exact ⟨by ring, by ring, by ring, by ring⟩

theorem denominator_powers_negative {q : ℝ} (hq : 4 < q) :
    8 - 2 * q < 0 ∧ 4 - q < 0 ∧ 3 - q < 0 := by
  exact ⟨by linarith, by linarith, by linarith⟩

theorem denominator_factors_le_one {q ν : ℝ} (hq : 4 < q) (hν : 1 ≤ ν) :
    ν ^ (8 - 2 * q) ≤ 1 ∧ ν ^ (4 - q) ≤ 1 ∧ ν ^ (3 - q) ≤ 1 := by
  have hs := denominator_powers_negative hq
  exact ⟨Real.rpow_le_one_of_one_le_of_nonpos hν hs.1.le,
    Real.rpow_le_one_of_one_le_of_nonpos hν hs.2.1.le,
    Real.rpow_le_one_of_one_le_of_nonpos hν hs.2.2.le⟩

theorem block_powers (q : ℝ) (hq : q ≠ 0) :
    blockPower q (q / 2) (q / 2) = -1 / 2 + 11 / (17 * q) ∧
    blockPower q 1 (2 * q - 5) = -1 / 2 - 6 / (17 * q) ∧
    blockPower q (q - 2) (q - 3) = 1 / 2 - 131 / (34 * q) ∧
    blockPower q (3 * q / 4 - 2) (5 * q / 4 - 2) = 1 / 4 - 57 / (17 * q) := by
  dsimp [blockPower]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> field_simp <;> ring

theorem block_powers_negative {q : ℝ} (hq : 4 < q) (hqu : q ≤ 9 / 2) :
    -1 / 2 + 11 / (17 * q) < 0 ∧ -1 / 2 - 6 / (17 * q) < 0 ∧
    1 / 2 - 131 / (34 * q) < 0 ∧ 1 / 4 - 57 / (17 * q) < 0 := by
  have h17 : 0 < 17 * q := by linarith
  have h34 : 0 < 34 * q := by linarith
  have h1 : 11 / (17 * q) < (1 : ℝ) / 2 :=
    (div_lt_iff₀ h17).mpr (by linarith)
  have h2 : 0 < 6 / (17 * q) := div_pos (by norm_num) h17
  have h3 : (1 : ℝ) / 2 < 131 / (34 * q) :=
    (lt_div_iff₀ h34).mpr (by linarith)
  have h4 : (1 : ℝ) / 4 < 57 / (17 * q) :=
    (lt_div_iff₀ h17).mpr (by linarith)
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem four_endpoint_antitone (q h m n₀ n₁ : ℝ)
    (hq : 4 < q) (hqu : q ≤ 9 / 2) (hn : n₀ ≤ n₁) :
    endpointExponent q (q / 2) (q / 2) h m n₁ ≤
      endpointExponent q (q / 2) (q / 2) h m n₀ ∧
    endpointExponent q 1 (2 * q - 5) h m n₁ ≤
      endpointExponent q 1 (2 * q - 5) h m n₀ ∧
    endpointExponent q (q - 2) (q - 3) h m n₁ ≤
      endpointExponent q (q - 2) (q - 3) h m n₀ ∧
    endpointExponent q (3 * q / 4 - 2) (5 * q / 4 - 2) h m n₁ ≤
      endpointExponent q (3 * q / 4 - 2) (5 * q / 4 - 2) h m n₀ := by
  have hp := block_powers q (by linarith)
  have hs := block_powers_negative hq hqu
  exact ⟨endpoint_antitone _ _ _ _ _ _ _ (by rw [hp.1]; exact hs.1.le) hn,
    endpoint_antitone _ _ _ _ _ _ _ (by rw [hp.2.1]; exact hs.2.1.le) hn,
    endpoint_antitone _ _ _ _ _ _ _ (by rw [hp.2.2.1]; exact hs.2.2.1.le) hn,
    endpoint_antitone _ _ _ _ _ _ _ (by rw [hp.2.2.2]; exact hs.2.2.2.le) hn⟩

/-- Actual positive real monomials, including the replacement third term. -/
theorem four_monomial_comparisons {K L q : ℝ} (hL : 1 ≤ L) (hLK : L ≤ K)
    (hq : 4 < q) (hqu : q ≤ 9 / 2)
    (hf : K ^ (q - 4) ≤ L ^ (6 - q))
    (hs : L ^ (3 * q - 8) ≤ K ^ (8 - q)) :
    K * L ^ (2 * q - 5) ≤ (K * L) ^ (q / 2) ∧
    K ^ (q - 2) * L ^ (q - 3) ≤ (K * L) ^ (q / 2) ∧
    K ^ (3 * q / 4 - 2) * L ^ (5 * q / 4 - 2) ≤ (K * L) ^ (q / 2) := by
  have hL0 : 0 < L := by linarith
  have hK0 : 0 < K := by linarith
  have hfl := (Real.log_le_log_iff (Real.rpow_pos_of_pos hK0 _)
    (Real.rpow_pos_of_pos hL0 _)).2 hf
  have hsl := (Real.log_le_log_iff (Real.rpow_pos_of_pos hL0 _)
    (Real.rpow_pos_of_pos hK0 _)).2 hs
  rw [Real.log_rpow hK0, Real.log_rpow hL0] at hfl
  rw [Real.log_rpow hK0, Real.log_rpow hL0] at hsl
  refine ⟨?_, ?_, ?_⟩
  · have hb := FirstSpacingConsequences.second_log_comparison
      (Real.log_nonneg hL) hq hqu hsl
    simpa using FirstSpacingConsequences.log_monomial_le hK0 hL0
      (a := 1) (b := 2 * q - 5) (c := q / 2) (by simpa using hb)
  · exact FirstSpacingConsequences.log_monomial_le hK0 hL0 (by nlinarith)
  · exact FirstSpacingConsequences.log_monomial_le hK0 hL0 (by nlinarith)

theorem fourTerm_le {K L q : ℝ} (hL : 1 ≤ L) (hLK : L ≤ K)
    (hq : 4 < q) (hqu : q ≤ 9 / 2)
    (hf : K ^ (q - 4) ≤ L ^ (6 - q))
    (hs : L ^ (3 * q - 8) ≤ K ^ (8 - q)) :
    fourTerm K L q ≤ 4 * (K * L) ^ (q / 2) := by
  have hh := four_monomial_comparisons hL hLK hq hqu hf hs
  unfold fourTerm
  linarith [hh.1, hh.2.1, hh.2.2]

/-- Uniform numerical margins at the new rational target. The final two
coordinates are `log_T(R²/H)` and `log_T(MR²/(HN²))`. -/
theorem caseA_six_margins {h m ell : ℝ} (hr : HardRange theta h m)
    (he0 : 0 ≤ ell) (he1 : ell ≤ 1 / 1000) :
    1 / 1000 ≤ radiusExponent m (blockA h m ell) ∧
    1 / 1000 ≤ h - radiusExponent m (blockA h m ell) ∧
    1 / 1000 ≤ blockA h m ell - h ∧
    1 / 1000 ≤ m - blockA h m ell ∧
    1 / 1000 ≤ 2 * radiusExponent m (blockA h m ell) - h ∧
    1 / 1000 ≤ m + 2 * radiusExponent m (blockA h m ell) - h -
      2 * blockA h m ell := by
  rcases hr with ⟨h0, h1, h2, hm⟩
  dsimp [theta] at h0 h1 h2
  dsimp [radiusExponent, blockA]
  exact ⟨by linarith, by linarith, by linarith, by linarith,
    by linarith, by linarith⟩

theorem small_log_conditions {ell : ℝ} (he : ell ≤ 1 / 1000) :
    969 * ell / 16100 ≤ -2 / 23 - (68 - 328 * theta) / 345 ∧
    969 * ell / 14000 ≤ (202 * theta - 50 - 53 / 4) / 75 := by
  dsimp [theta]
  constructor <;> linarith

theorem arithmetic_cases_cover {h m ell : ℝ} (hr : HardRange theta h m)
    (he : ell ≤ 1 / 1000) :
    (caseBoundary m ell ≤ h ∧ h < m - 49 / 164) ∨
    (h < caseBoundary m ell ∧ h ≤ 35 * m / 69 - 2 / 23 ∧
      137 / 7312 < 3 * m / 2 - 1 / 2 - h ∧
      blockA h m ell ≤ min (blockB₁ h m ell) (blockB₂ h m)) := by
  by_cases hb : caseBoundary m ell ≤ h
  · refine Or.inl ⟨hb, ?_⟩
    have hh := hr.2.1
    dsimp [theta] at hh
    linarith
  have hb' : h < caseBoundary m ell := lt_of_not_ge hb
  have hs := small_log_conditions he
  have hp := phase_constant_margin theta h m hr
  refine Or.inr ⟨hb', caseB_first_upper theta h m ell hr.2.1 hb'.le hs.1, ?_,
    blockA_le_blockB theta h m ell hr hb'.le hs.2⟩
  norm_num [theta] at hp
  exact hp

theorem caseB_six_margins {h m ell n : ℝ} (hr : HardRange theta h m)
    (he0 : 0 ≤ ell) (he1 : ell ≤ 1 / 1000)
    (hb : h ≤ caseBoundary m ell)
    (hn0 : blockA h m ell ≤ n) (hn1 : n ≤ blockB₂ h m) :
    1 / 1000 ≤ radiusExponent m n ∧
    1 / 1000 ≤ h - radiusExponent m n ∧
    1 / 1000 ≤ n - h ∧ 1 / 1000 ≤ m - n ∧
    1 / 1000 ≤ 2 * radiusExponent m n - h ∧
    1 / 1000 ≤ m + 2 * radiusExponent m n - h - 2 * n := by
  rcases hr with ⟨h0, h1, h2, hm⟩
  dsimp [theta] at h0 h1 h2
  dsimp [blockA] at hn0
  dsimp [blockB₂] at hn1
  dsimp [caseBoundary] at hb
  dsimp [radiusExponent]
  exact ⟨by linarith, by linarith, by linarith, by linarith,
    by linarith, by linarith⟩

/-- The actual four finite moment endpoint exponents, with the logarithmic
correction included, stay below `h + theta` at the reference length. -/
theorem square_root_endpoint_le {h m ell : ℝ} (hr : HardRange theta h m)
    (he : 0 ≤ ell) :
    endpointExponent (qHat (h-m)) (qHat (h-m) / 2) (qHat (h-m) / 2)
      h m (blockA h m ell) ≤ h + theta := by
  have hx : hardInterval (h-m) := hard_ratio_range theta h m hr
  have hq := qHat_range (h-m)
  have hE := (four_moment_optimization hx).2.2
  have hid := square_root_endpoint_exponent (qHat (h-m)) h m ell (by linarith)
  have hn := (block_powers_negative hq.1 hq.2).1
  have hnon : (-1 / 2 + 11 / (17 * qHat (h-m))) * (969 * ell / 14000) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hn.le (by positivity)
  change E (h-m) (qHat (h-m)) ≤ theta at hE
  dsimp [E] at hE
  linarith

/-- All four complete endpoint exponents are bounded, including every
logarithmic power. This directly verifies the finite-moment substitution
without first claiming square-root behavior at larger denominators. -/
theorem four_reference_endpoint_bounds {h m ell : ℝ} (hr : HardRange theta h m)
    (he : 0 ≤ ell) :
    endpointExponent (qHat (h-m)) (qHat (h-m) / 2) (qHat (h-m) / 2)
      h m (blockA h m ell) ≤ h + theta ∧
    endpointExponent (qHat (h-m)) 1 (2 * qHat (h-m) - 5)
      h m (blockA h m ell) ≤ h + theta ∧
    endpointExponent (qHat (h-m)) (qHat (h-m) - 2) (qHat (h-m) - 3)
      h m (blockA h m ell) ≤ h + theta ∧
    endpointExponent (qHat (h-m)) (3 * qHat (h-m) / 4 - 2)
      (5 * qHat (h-m) / 4 - 2) h m (blockA h m ell) ≤ h + theta := by
  rcases hr with ⟨h0, h1, h2, hm⟩
  dsimp [theta] at h0 h1 h2 ⊢
  unfold qHat
  split_ifs with ha hb hc
  all_goals norm_num [endpointExponent, radiusExponent, kExponent, lExponent, blockA]
  all_goals exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- Increasing the actual block length above the reference improves each
complete endpoint term, and hence preserves the final exponent. -/
theorem four_actual_endpoint_bounds {h m ell n : ℝ} (hr : HardRange theta h m)
    (he : 0 ≤ ell) (hn : blockA h m ell ≤ n) :
    endpointExponent (qHat (h-m)) (qHat (h-m) / 2) (qHat (h-m) / 2)
      h m n ≤ h + theta ∧
    endpointExponent (qHat (h-m)) 1 (2 * qHat (h-m) - 5)
      h m n ≤ h + theta ∧
    endpointExponent (qHat (h-m)) (qHat (h-m) - 2) (qHat (h-m) - 3)
      h m n ≤ h + theta ∧
    endpointExponent (qHat (h-m)) (3 * qHat (h-m) / 4 - 2)
      (5 * qHat (h-m) / 4 - 2) h m n ≤ h + theta := by
  have hq := qHat_range (h-m)
  have hb := four_reference_endpoint_bounds hr he
  have ha := four_endpoint_antitone (qHat (h-m)) h m (blockA h m ell) n hq.1 hq.2 hn
  exact ⟨ha.1.trans hb.1, ha.2.1.trans hb.2.1,
    ha.2.2.1.trans hb.2.2.1, ha.2.2.2.trans hb.2.2.2⟩

end
end CircleDivisor.EnergyV3.Arithmetic
