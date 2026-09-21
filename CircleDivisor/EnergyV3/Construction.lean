import CircleDivisor.EnergyV3.Arithmetic

/-! Subsidiary construction exponents and actual scale inequalities. These are
internal consequences of the displayed block lengths, with explicit margins.
No second-spacing or resonance-curve theorem is proved or assumed here. -/

namespace CircleDivisor.EnergyV3.Construction
noncomputable section
open CircleDivisor.Arithmetic CircleDivisor.ExternalInterfaces

def v₀ (h m n : ℝ) := 18 / 17 * (h - radiusExponent m n)
def v₁ (h m n : ℝ) := 4 * radiusExponent m n - h - n
def v₂ (h m n : ℝ) := 2 * m - h - 3 * n

theorem caseA_subsidiary_identities (h m ell : ℝ) :
    v₁ h m (blockA h m ell) - v₀ h m (blockA h m ell) =
      (h + 9 * m - 4 - 171 * ell / 140) / 5 ∧
    v₂ h m (blockA h m ell) - v₀ h m (blockA h m ell) =
      (h + 6 - 11 * m - 171 * ell / 140) / 5 := by
  dsimp [v₀, v₁, v₂, radiusExponent, blockA]
  constructor <;> ring

theorem shortening_subsidiary_ratio (h m n s : ℝ) :
    v₁ h m (n-s) - v₀ h m (n-s) = v₁ h m n - v₀ h m n + 60 / 17 * s ∧
    v₂ h m (n-s) - v₀ h m (n-s) = v₂ h m n - v₀ h m n + 60 / 17 * s := by
  dsimp [v₀, v₁, v₂, radiusExponent]
  constructor <;> ring

theorem caseA_subsidiary_ratios {h m ell : ℝ} (hm : m ≤ 1 / 2)
    (hb : caseBoundary m ell ≤ h) :
    v₀ h m (blockA h m ell) ≤ v₁ h m (blockA h m ell) ∧
    v₀ h m (blockA h m ell) ≤ v₂ h m (blockA h m ell) := by
  have hi := caseA_subsidiary_identities h m ell
  dsimp [caseBoundary] at hb
  constructor <;> linarith [hi.1, hi.2]

theorem caseB_v₁_nonneg {h m n : ℝ} (hn : n ≤ blockB₂ h m) :
    0 ≤ v₁ h m n := by
  dsimp [v₁, radiusExponent]
  dsimp [blockB₂] at hn
  linarith

theorem caseB_v₂_margin {h m ell n : ℝ} (hr : HardRange theta h m)
    (he : ell ≤ 1 / 1000) (hn : n ≤ blockB₁ h m ell) :
    1 / 10 ≤ v₂ h m n := by
  rcases hr with ⟨h0, h1, h2, hm⟩
  dsimp [theta] at h0 h1 h2
  dsimp [blockB₁] at hn
  dsimp [v₂]
  linarith

/-- The source denominator-range upper restriction has a fixed positive
power margin, rather than merely holding pointwise. -/
theorem denominator_range_margin {h m n : ℝ} (hr : HardRange theta h m)
    (hradius : 1 / 1000 ≤ 2 * radiusExponent m n - h) :
    1 / 1000 ≤ 357 / 487 * (h + 1 - 2 * m) - (h - radiusExponent m n) := by
  rcases hr with ⟨h0, h1, h2, hm⟩
  dsimp [theta] at h0 h1 h2
  linarith

/-- The further construction requirement `MR²/(HN) >> V₀²` in Case A. -/
theorem caseA_further_margin {h m ell : ℝ} (hr : HardRange theta h m)
    (he0 : 0 ≤ ell) (he1 : ell ≤ 1 / 1000) :
    1 / 1000 ≤ m + 2 * radiusExponent m (blockA h m ell) - h -
      blockA h m ell - 2 * v₀ h m (blockA h m ell) := by
  rcases hr with ⟨h0, h1, h2, hm⟩
  dsimp [theta] at h0 h1 h2
  dsimp [radiusExponent, blockA, v₀]
  linarith

/-- The further construction requirement in the selected Case B branch. -/
theorem caseB_further_margin {h m ell n : ℝ} (hr : HardRange theta h m)
    (he : ell ≤ 1 / 1000) (hn : n ≤ blockB₁ h m ell) :
    1 / 1000 ≤ m + 2 * radiusExponent m n - h - n - 2 * v₀ h m n := by
  rcases hr with ⟨h0, h1, h2, hm⟩
  dsimp [theta] at h0 h1 h2
  dsimp [blockB₁] at hn
  dsimp [radiusExponent, v₀]
  linarith

/-- Explicitly absorb constants and rounding comparability in the two
additional standing conditions. The hypotheses on N and R are only ordinary
positive real comparisons, not any analytic estimate. -/
theorem extra_standing_of_margins {D C T h m n r N R d : ℝ}
    (hD : 1 ≤ D) (hC : 1 ≤ C) (hT : 1 ≤ T) (hh : 0 ≤ h)
    (hN : 0 < N) (hR : 0 < R)
    (hn : Comparable D N (T ^ n)) (hr : Comparable D R (T ^ r))
    (hgapR : d ≤ 2 * r - h) (hgapN : d ≤ m + 2 * r - h - 2 * n)
    (hlargeR : (2 * C + 1) * D ≤ T ^ (d / 2))
    (hlargeN : D ^ 4 ≤ T ^ d) :
    2 * C * Real.sqrt (T ^ h) + 1 ≤ R ∧
    T ^ h * N ^ 2 ≤ T ^ m * R ^ 2 := by
  have hDp : 0 < D := by linarith
  have hTp : 0 < T := by linarith
  have hrlo : T ^ r ≤ R * D := (div_le_iff₀ hDp).mp hr.1
  have hsqrt : Real.sqrt (T ^ h) = T ^ (h / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hTp.le]
    congr 1
    ring
  have hsqrt1 : 1 ≤ T ^ (h / 2) := Real.one_le_rpow hT (by linarith)
  have hRcoef := CircleDivisor.BlockSeparation.factor_rpow_le T (d/2) (h/2) r
    ((2*C+1)*D) hT (by linarith) hlargeR
  have hRmain : (2 * C + 1) * T ^ (h / 2) ≤ R := by
    have hm : ((2 * C + 1) * T ^ (h / 2)) * D ≤ R * D := by
      calc
        _ = ((2*C+1)*D) * T ^ (h/2) := by ring
        _ ≤ T ^ r := hRcoef
        _ ≤ R * D := hrlo
    nlinarith
  refine ⟨?_, ?_⟩
  · rw [hsqrt]
    nlinarith
  have hN2 : N ^ 2 ≤ D ^ 2 * T ^ (2 * n) := by
    have hb := (sq_le_sq₀ hN.le (show 0 ≤ D * T ^ n by positivity)).2 hn.2
    have he : (D * T ^ n) ^ 2 = D ^ 2 * T ^ (2*n) := by
      rw [mul_pow, show 2*n=n*2 by ring, Real.rpow_mul hTp.le, Real.rpow_two]
    rwa [he] at hb
  have hR2 : T ^ (2 * r) ≤ D ^ 2 * R ^ 2 := by
    have hb := (sq_le_sq₀ (show 0 ≤ T ^ r by positivity)
      (show 0 ≤ R * D by positivity)).2 hrlo
    have he : (T ^ r) ^ 2 = T ^ (2*r) := by
      rw [show 2*r=r*2 by ring, Real.rpow_mul hTp.le, Real.rpow_two]
    rw [he, mul_pow] at hb
    nlinarith
  have hpow := CircleDivisor.BlockSeparation.factor_rpow_le T d (h+2*n) (m+2*r)
    (D^4) hT (by linarith) hlargeN
  have hmul : D ^ 2 * (T ^ h * N ^ 2) ≤ D ^ 2 * (T ^ m * R ^ 2) := by
    calc
      D ^ 2 * (T ^ h * N ^ 2) ≤ D ^ 2 * (T ^ h * (D ^ 2 * T ^ (2*n))) := by
        gcongr
      _ = D ^ 4 * T ^ (h+2*n) := by rw [Real.rpow_add hTp]; ring
      _ ≤ T ^ (m+2*r) := hpow
      _ = T ^ m * T ^ (2*r) := Real.rpow_add hTp _ _
      _ ≤ T ^ m * (D ^ 2 * R ^ 2) := by gcongr
      _ = D ^ 2 * (T ^ m * R ^ 2) := by ring
  exact (mul_le_mul_iff_right₀ (pow_pos hDp 2)).mp hmul

/-- All fixed factors needed for both extra standing conditions are absorbed
at one uniform threshold. -/
theorem extra_standing_threshold (D C d : ℝ) (hd : 0 < d) :
    ∃ T₀ : ℝ, 1 ≤ T₀ ∧ ∀ T ≥ T₀,
      (2 * C + 1) * D ≤ T ^ (d / 2) ∧ D ^ 4 ≤ T ^ d := by
  obtain ⟨T1, h1⟩ := Filter.tendsto_atTop_atTop.mp
    (tendsto_rpow_atTop (show 0 < d/2 by linarith)) ((2*C+1)*D)
  obtain ⟨T2, h2⟩ := Filter.tendsto_atTop_atTop.mp
    (tendsto_rpow_atTop hd) (D^4)
  refine ⟨max 1 (max T1 T2), le_max_left _ _, fun T hT => ?_⟩
  exact ⟨h1 T ((le_max_left T1 T2).trans ((le_max_right 1 _).trans hT)),
    h2 T ((le_max_right T1 T2).trans ((le_max_right 1 _).trans hT))⟩

end
end CircleDivisor.EnergyV3.Construction
