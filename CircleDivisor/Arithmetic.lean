import Mathlib

/-!
# Exact arithmetic of Sections 5 and 6.1–6.3

All variables in this file are real logarithmic exponents: `h = log_T H`,
`m = log_T M`, and `ell = log_T (log T)`.  The results are exact algebraic
statements.  They do not assume an analytic large-sieve or spacing estimate.
The small positive margins proved below are what permit logarithmic factors
and fixed construction constants to be absorbed for sufficiently large `T`.
-/

namespace CircleDivisor.Arithmetic

noncomputable section

/-- Exponent of `Q/R₀` after volume comparison and the qth-power large sieve. -/
def denominatorPower (q a b : ℝ) : ℝ := a + b + 8 - 3 * q

/-- Exponent of `N` after taking the qth root. -/
def blockPower (q a b : ℝ) : ℝ :=
  -(3 : ℝ) / 2 + 11 / (17 * q) + (3 * a + b) / (2 * q)

theorem denominatorPower_origin (q a b : ℝ) (hq : q ≠ 0) :
    (-(3 - 6 / q) * q + 2 + a + b) = denominatorPower q a b := by
  unfold denominatorPower
  field_simp
  ring

theorem denominator_powers (q : ℝ) :
    denominatorPower q (q / 2) (q / 2) = 8 - 2 * q ∧
    denominatorPower q 1 (2 * q - 5) = 4 - q ∧
    denominatorPower q (q - 2) ((q - 1) / 2) = (11 - 3 * q) / 2 ∧
    denominatorPower q (3 * q / 4 - 2) (5 * q / 4 - 2) = 4 - q := by
  dsimp [denominatorPower]
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

theorem denominator_powers_nonpositive (q : ℝ) (hq : 4 < q) :
    8 - 2 * q ≤ 0 ∧ 4 - q ≤ 0 ∧ (11 - 3 * q) / 2 ≤ 0 := by
  constructor
  · linarith
  constructor <;> linarith

theorem block_powers (q : ℝ) (hq : q ≠ 0) :
    blockPower q (q / 2) (q / 2) = -1 / 2 + 11 / (17 * q) ∧
    blockPower q 1 (2 * q - 5) = -1 / 2 - 6 / (17 * q) ∧
    blockPower q (q - 2) ((q - 1) / 2) = 1 / 4 - 177 / (68 * q) ∧
    blockPower q (3 * q / 4 - 2) (5 * q / 4 - 2) = 1 / 4 - 57 / (17 * q) := by
  dsimp [blockPower]
  constructor
  · field_simp
    ring
  constructor
  · field_simp
    ring
  constructor <;> field_simp <;> ring

theorem block_powers_negative (q : ℝ) (hq : 4 < q) (hq' : q ≤ 9 / 2) :
    -1 / 2 + 11 / (17 * q) < 0 ∧
    -1 / 2 - 6 / (17 * q) < 0 ∧
    1 / 4 - 177 / (68 * q) < 0 ∧
    1 / 4 - 57 / (17 * q) < 0 := by
  have h17 : 0 < 17 * q := by linarith
  have h68 : 0 < 68 * q := by linarith
  have h₁ : 11 / (17 * q) < (1 : ℝ) / 2 :=
    (div_lt_iff₀ h17).mpr (by linarith)
  have h₂ : 0 < 6 / (17 * q) := div_pos (by norm_num) h17
  have h₃ : (1 : ℝ) / 4 < 177 / (68 * q) :=
    (lt_div_iff₀ h68).mpr (by linarith)
  have h₄ : (1 : ℝ) / 4 < 57 / (17 * q) :=
    (lt_div_iff₀ h17).mpr (by linarith)
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

def radiusExponent (m n : ℝ) : ℝ := (3 * m - n - 1) / 2
def kExponent (m n : ℝ) : ℝ := n - radiusExponent m n
def lExponent (h m n : ℝ) : ℝ := h - radiusExponent m n

/-- Exponent in the endpoint `|S|` bound belonging to the monomial `K^a L^b`. -/
def endpointExponent (q a b h m n : ℝ) : ℝ :=
  m + radiusExponent m n - n + 22 / (17 * q) * lExponent h m n +
    (a * kExponent m n + b * lExponent h m n) / q

theorem endpoint_block_difference (q a b h m n₀ n₁ : ℝ) :
    endpointExponent q a b h m n₁ - endpointExponent q a b h m n₀ =
      blockPower q a b * (n₁ - n₀) := by
  dsimp [endpointExponent, radiusExponent, kExponent, lExponent, blockPower]
  ring

theorem endpoint_antitone (q a b h m n₀ n₁ : ℝ)
    (hp : blockPower q a b ≤ 0) (hn : n₀ ≤ n₁) :
    endpointExponent q a b h m n₁ ≤ endpointExponent q a b h m n₀ := by
  have he := endpoint_block_difference q a b h m n₀ n₁
  have hm : blockPower q a b * (n₁ - n₀) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hp (sub_nonneg.mpr hn)
  linarith

theorem four_endpoint_antitone (q h m n₀ n₁ : ℝ)
    (hq : 4 < q) (hq' : q ≤ 9 / 2) (hn : n₀ ≤ n₁) :
    endpointExponent q (q / 2) (q / 2) h m n₁ ≤
      endpointExponent q (q / 2) (q / 2) h m n₀ ∧
    endpointExponent q 1 (2 * q - 5) h m n₁ ≤
      endpointExponent q 1 (2 * q - 5) h m n₀ ∧
    endpointExponent q (q - 2) ((q - 1) / 2) h m n₁ ≤
      endpointExponent q (q - 2) ((q - 1) / 2) h m n₀ ∧
    endpointExponent q (3 * q / 4 - 2) (5 * q / 4 - 2) h m n₁ ≤
      endpointExponent q (3 * q / 4 - 2) (5 * q / 4 - 2) h m n₀ := by
  have hp := block_powers q (by linarith)
  have hs := block_powers_negative q hq hq'
  exact ⟨endpoint_antitone _ _ _ _ _ _ _ (by rw [hp.1]; exact hs.1.le) hn,
    endpoint_antitone _ _ _ _ _ _ _ (by rw [hp.2.1]; exact hs.2.1.le) hn,
    endpoint_antitone _ _ _ _ _ _ _ (by rw [hp.2.2.1]; exact hs.2.2.1.le) hn,
    endpoint_antitone _ _ _ _ _ _ _ (by rw [hp.2.2.2]; exact hs.2.2.2.le) hn⟩

def blockA (h m ell : ℝ) : ℝ :=
  41 * m / 25 - 16 * h / 25 - 49 / 100 + 969 * ell / 14000
def blockB₁ (h m ell : ℝ) : ℝ :=
  7 * m / 8 - 29 * h / 40 - 3 / 20 + 969 * ell / 5600
def blockB₂ (h m : ℝ) : ℝ := 2 * m - h / 3 - 2 / 3
def caseBoundary (m ell : ℝ) : ℝ := -9 * m + 4 + 171 * ell / 140

theorem blockB₁_sub_blockA (h m ell : ℝ) :
    blockB₁ h m ell - blockA h m ell =
      17 / 200 * (caseBoundary m ell - h) := by
  unfold blockB₁ blockA caseBoundary
  ring

theorem blockB₂_sub_blockA (h m ell : ℝ) :
    blockB₂ h m - blockA h m ell =
      (23 * h + 27 * m - 53 / 4) / 75 - 969 * ell / 14000 := by
  unfold blockB₂ blockA
  ring

/-- The exact interpolation in (6.5), including its logarithmic exponent. -/
theorem case_interpolation_identity (theta m ell : ℝ) :
    328 / 345 * (m - theta) + 17 / 345 * caseBoundary m ell =
      35 * m / 69 + (68 - 328 * theta) / 345 + 969 * ell / 16100 := by
  unfold caseBoundary
  ring

theorem case_interpolation (theta h m ell : ℝ)
    (hh : h ≤ m - theta) (hb : h ≤ caseBoundary m ell) :
    h ≤ 35 * m / 69 + (68 - 328 * theta) / 345 + 969 * ell / 16100 := by
  rw [← case_interpolation_identity]
  linarith

/-- The three excluded ranges are exactly the trivial and one-dimensional regimes. -/
def HardRange (theta h m : ℝ) : Prop :=
  (7 * theta - 2) / 2 < h ∧ h ≤ m - theta ∧
    m + 2 * theta - 1 < h ∧ m ≤ 1 / 2

theorem easy_or_hard (theta h m : ℝ)
    (hupper : h ≤ m - theta) (mupper : m ≤ 1 / 2) :
    (h + 1) * (2 / 7) ≤ theta ∨
    (h + 1 - m) / 2 ≤ theta ∨ HardRange theta h m := by
  by_cases h₁ : h ≤ (7 * theta - 2) / 2
  · exact Or.inl (by linarith)
  by_cases h₂ : h ≤ m + 2 * theta - 1
  · exact Or.inr (Or.inl (by linarith))
  exact Or.inr (Or.inr ⟨lt_of_not_ge h₁, hupper, lt_of_not_ge h₂, mupper⟩)

theorem hard_ratio_range (theta h m : ℝ) (hr : HardRange theta h m) :
    2 * theta - 1 < h - m ∧ h - m ≤ -theta := by
  rcases hr with ⟨_, h₂, h₃, _⟩
  constructor <;> linarith

theorem hard_m_lower (theta h m : ℝ) (hr : HardRange theta h m) :
    (9 * theta - 2) / 2 < m := by
  rcases hr with ⟨h₁, h₂, _, _⟩
  linarith

theorem phase_constant_margin (theta h m : ℝ) (hr : HardRange theta h m) :
    (13 * theta - 4) / 4 < 3 * m / 2 - 1 / 2 - h := by
  rcases hr with ⟨h₁, h₂, _, _⟩
  linarith

theorem second_block_margin (theta h m : ℝ) (hr : HardRange theta h m) :
    202 * theta - 50 < 23 * h + 27 * m := by
  rcases hr with ⟨h₁, h₂, _, _⟩
  linarith

def ThetaWindow (theta : ℝ) : Prop :=
  313461 / 1000000 < theta ∧ theta < 313462 / 1000000

/-- Every fixed numerical threshold used before the optimization. -/
theorem theta_thresholds (theta : ℝ) (ht : ThetaWindow theta) :
    49 / 164 < theta ∧ 4 / 13 < theta ∧ 253 / 808 < theta ∧
    5 / 16 < theta ∧ 89 / 284 < theta ∧ 1 / 4 < theta ∧ theta < 1 / 3 := by
  rcases ht with ⟨hl, hu⟩
  exact ⟨by linarith, by linarith, by linarith, by linarith,
    by linarith, by linarith, by linarith⟩

theorem positive_power_margins (theta : ℝ) (ht : ThetaWindow theta) :
    0 < (13 * theta - 4) / 4 ∧
    53 / 4 < 202 * theta - 50 ∧
    (68 - 328 * theta) / 345 < -2 / 23 ∧
    0 < 34 * theta / 25 - 17 / 40 ∧
    0 < (9 * theta - 2) / 2 + 8 / 25 * (2 * theta - 1) - 51 / 200 ∧
    0 < (17 * theta - 5) / 3 := by
  rcases ht with ⟨hl, hu⟩
  exact ⟨by linarith, by linarith, by linarith, by linarith,
    by linarith, by linarith⟩

/-- Case A's upper condition follows from the target H range. -/
theorem caseA_upper (theta h m : ℝ) (ht : ThetaWindow theta)
    (hh : h ≤ m - theta) : h < m - 49 / 164 := by
  have hx := (theta_thresholds theta ht).1
  linarith

/-- Explicit logarithmic control, without asymptotic notation, suffices for Case B. -/
theorem caseB_first_upper (theta h m ell : ℝ)
    (hh : h ≤ m - theta) (hb : h ≤ caseBoundary m ell)
    (he : 969 * ell / 16100 ≤ -2 / 23 - (68 - 328 * theta) / 345) :
    h ≤ 35 * m / 69 - 2 / 23 := by
  have hi := case_interpolation theta h m ell hh hb
  linarith

theorem blockA_le_blockB₁ (h m ell : ℝ) (hb : h ≤ caseBoundary m ell) :
    blockA h m ell ≤ blockB₁ h m ell := by
  have he := blockB₁_sub_blockA h m ell
  linarith

theorem blockA_le_blockB₂ (theta h m ell : ℝ) (hr : HardRange theta h m)
    (he : 969 * ell / 14000 ≤ (202 * theta - 50 - 53 / 4) / 75) :
    blockA h m ell < blockB₂ h m := by
  have hm := second_block_margin theta h m hr
  have hid := blockB₂_sub_blockA h m ell
  linarith

theorem blockA_le_blockB (theta h m ell : ℝ) (hr : HardRange theta h m)
    (hb : h ≤ caseBoundary m ell)
    (he : 969 * ell / 14000 ≤ (202 * theta - 50 - 53 / 4) / 75) :
    blockA h m ell ≤ min (blockB₁ h m ell) (blockB₂ h m) := by
  exact le_min (blockA_le_blockB₁ h m ell hb) (blockA_le_blockB₂ theta h m ell hr he).le

def kappa (x : ℝ) : ℝ := -47 / 200 - 24 * x / 25
def lambda (x : ℝ) : ℝ := 51 / 200 + 17 * x / 25

/-- Appendix A and (6.11), with every logarithmic correction retained. -/
theorem endpoint_parameter_identities (h m ell : ℝ) :
    blockA h m ell - m = -16 * (h - m) / 25 - 49 / 100 + 969 * ell / 14000 ∧
    radiusExponent m (blockA h m ell) - m =
      8 * (h - m) / 25 - 51 / 200 - 969 * ell / 28000 ∧
    kExponent m (blockA h m ell) = kappa (h - m) + 2907 * ell / 28000 ∧
    lExponent h m (blockA h m ell) = lambda (h - m) + 969 * ell / 28000 ∧
    kExponent m (blockA h m ell) + lExponent h m (blockA h m ell) =
      1 / 50 - 7 * (h - m) / 25 + 969 * ell / 7000 ∧
    blockA h m ell - h = -41 * (h - m) / 25 - 49 / 100 + 969 * ell / 14000 := by
  dsimp [blockA, radiusExponent, kExponent, lExponent, kappa, lambda]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ring

theorem hard_spacing_separations (theta h m : ℝ)
    (ht : ThetaWindow theta) (hr : HardRange theta h m) :
    -3 / 8 < h - m ∧
    0 < lambda (h - m) ∧
    0 < blockA h m 0 - h ∧
    blockA h m 0 - m < 0 ∧
    0 < radiusExponent m (blockA h m 0) ∧
    lambda (h - m) < kappa (h - m) := by
  rcases ht with ⟨hl, hu⟩
  rcases hr with ⟨h₁, h₂, h₃, hm⟩
  dsimp [lambda, blockA, radiusExponent, kappa]
  exact ⟨by linarith, by linarith, by linarith, by linarith,
    by linarith, by linarith⟩

theorem radius_lower_margin (theta h m : ℝ) (hr : HardRange theta h m) :
    (9 * theta - 2) / 2 + 8 / 25 * (2 * theta - 1) - 51 / 200 <
      radiusExponent m (blockA h m 0) := by
  have hm := hard_m_lower theta h m hr
  have hx := hard_ratio_range theta h m hr
  dsimp [radiusExponent, blockA]
  linarith

/-- The upper alternative in Case B keeps `N_B/M` strictly below a negative power. -/
theorem caseB_block_upper (theta h m n : ℝ) (hr : HardRange theta h m)
    (hn : n ≤ blockB₂ h m) : n - m ≤ -1 / 6 - h / 3 := by
  rcases hr with ⟨_, _, _, hm⟩
  dsimp [blockB₂] at hn
  linarith

/-- The same upper alternative also keeps the actual Case B spacing radius above 1. -/
theorem caseB_radius_lower (theta h m n : ℝ) (hr : HardRange theta h m)
    (hn : n ≤ blockB₂ h m) :
    (17 * theta - 5) / 3 < 2 * radiusExponent m n := by
  rcases hr with ⟨h₁, h₂, _, _⟩
  dsimp [blockB₂] at hn
  dsimp [radiusExponent]
  linarith

/-- Logarithmic exponent of the square-root interface after division by H. -/
theorem square_root_endpoint_exponent (q h m ell : ℝ) (hq : q ≠ 0) :
    endpointExponent q (q / 2) (q / 2) h m (blockA h m ell) - h =
      (-9 / 50 + 22 / (25 * q)) * (h - m) + 49 / 200 + 33 / (100 * q) +
        (-1 / 2 + 11 / (17 * q)) * (969 * ell / 14000) := by
  dsimp [endpointExponent, radiusExponent, kExponent, lExponent, blockA]
  field_simp
  ring

/-- A concrete upper bound on the logarithmic correction suffices for both
comparisons.  The separate analytic task is to prove `log_T (log T) ≤ 1/100`
eventually. -/
theorem small_log_conditions (theta ell : ℝ) (ht : ThetaWindow theta)
    (hell : ell ≤ 1 / 100) :
    969 * ell / 16100 ≤ -2 / 23 - (68 - 328 * theta) / 345 ∧
    969 * ell / 14000 ≤ (202 * theta - 50 - 53 / 4) / 75 := by
  rcases ht with ⟨hl, hu⟩
  constructor <;> linarith

/-- Both arithmetic cases cover the hard range, at the level of exponents,
with all logarithmic powers present. -/
theorem arithmetic_cases_cover (theta h m ell : ℝ)
    (ht : ThetaWindow theta) (hr : HardRange theta h m) (hell : ell ≤ 1 / 100) :
    (caseBoundary m ell ≤ h ∧ h < m - 49 / 164) ∨
    (h < caseBoundary m ell ∧ h ≤ 35 * m / 69 - 2 / 23 ∧
      0 < 3 * m / 2 - 1 / 2 - h ∧
      blockA h m ell ≤ min (blockB₁ h m ell) (blockB₂ h m)) := by
  by_cases hb : caseBoundary m ell ≤ h
  · exact Or.inl ⟨hb, caseA_upper theta h m ht hr.2.1⟩
  have hb' : h < caseBoundary m ell := lt_of_not_ge hb
  have he := small_log_conditions theta ell ht hell
  have hp := (positive_power_margins theta ht).1
  have hm := phase_constant_margin theta h m hr
  exact Or.inr ⟨hb', caseB_first_upper theta h m ell hr.2.1 hb'.le he.1,
    by linarith, blockA_le_blockB theta h m ell hr hb'.le he.2⟩

theorem hard_spacing_separations_with_logs (theta h m ell : ℝ)
    (ht : ThetaWindow theta) (hr : HardRange theta h m)
    (he₀ : 0 ≤ ell) (he₁ : ell ≤ 1 / 100) :
    0 < lExponent h m (blockA h m ell) ∧
    0 < blockA h m ell - h ∧
    blockA h m ell - m < 0 ∧
    0 < radiusExponent m (blockA h m ell) ∧
    lExponent h m (blockA h m ell) < kExponent m (blockA h m ell) := by
  rcases ht with ⟨hl, hu⟩
  rcases hr with ⟨h₁, h₂, h₃, hm⟩
  dsimp [lExponent, blockA, radiusExponent, kExponent]
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

/-- Validity of the larger Case B block's spacing scales follows from both
length comparisons; it need not be separately postulated as an input. -/
theorem actual_caseB_separations (theta h m ell n : ℝ)
    (ht : ThetaWindow theta) (hr : HardRange theta h m)
    (he₀ : 0 ≤ ell) (he₁ : ell ≤ 1 / 100)
    (hn₀ : blockA h m ell ≤ n) (hn₁ : n ≤ blockB₂ h m) :
    h < n ∧ 0 < lExponent h m n ∧ n < m ∧ 0 < radiusExponent m n := by
  have hs := hard_spacing_separations_with_logs theta h m ell ht hr he₀ he₁
  have hnupper := caseB_block_upper theta h m n hr hn₁
  have hrlower := caseB_radius_lower theta h m n hr hn₁
  have htpos := (positive_power_margins theta ht).2.2.2.2.2
  have hhpos : 0 < h := by
    have htlow := ht.1
    have hh := hr.1
    linarith
  have hlmono : lExponent h m (blockA h m ell) ≤ lExponent h m n := by
    dsimp [lExponent, radiusExponent]
    linarith
  exact ⟨by linarith [hs.2.1], lt_of_lt_of_le hs.1 hlmono,
    by linarith, by linarith⟩

theorem denominator_factors_le_one (q nu : ℝ) (hq : 4 < q) (hnu : 1 ≤ nu) :
    nu ^ (8 - 2 * q) ≤ 1 ∧ nu ^ (4 - q) ≤ 1 ∧ nu ^ ((11 - 3 * q) / 2) ≤ 1 := by
  have hs := denominator_powers_nonpositive q hq
  exact ⟨Real.rpow_le_one_of_one_le_of_nonpos hnu hs.1,
    Real.rpow_le_one_of_one_le_of_nonpos hnu hs.2.1,
    Real.rpow_le_one_of_one_le_of_nonpos hnu hs.2.2⟩

/-- Decay exponents for the maximal denominator scale and major-arc ratio. -/
theorem complementary_decay_exponents (q delta : ℝ) (hq : 4 < q)
    (hdelta : 0 < delta) :
    -80 / 119 * delta < 0 ∧ -(1 + 22 / (17 * q)) * delta < 0 := by
  have hden : 0 < 17 * q := by linarith
  have hquot : 0 < 22 / (17 * q) := div_pos (by norm_num) hden
  constructor
  · nlinarith
  · exact mul_neg_of_neg_of_pos (by linarith) hdelta

end

end CircleDivisor.Arithmetic
