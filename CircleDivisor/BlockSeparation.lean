import CircleDivisor.Arithmetic
import CircleDivisor.ExternalInterfaces

/-! Quantitative versions of the strict exponent separations in Section 6.3.
These supply a uniform margin, rather than a pointwise asymptotic threshold
depending on the particular h,m in the hard range. -/

namespace CircleDivisor.BlockSeparation
noncomputable section
open Arithmetic ExternalInterfaces Filter

theorem caseA_uniform_margin (theta h m ell : ℝ)
    (ht : ThetaWindow theta) (hr : HardRange theta h m)
    (he₀ : 0 ≤ ell) (he₁ : ell ≤ 1 / 100) :
    1 / 1000 ≤ radiusExponent m (blockA h m ell) ∧
    1 / 1000 ≤ h - radiusExponent m (blockA h m ell) ∧
    1 / 1000 ≤ blockA h m ell - h ∧
    1 / 1000 ≤ m - blockA h m ell := by
  rcases ht with ⟨ht₀, ht₁⟩
  rcases hr with ⟨hh₀, hh₁, hh₂, hm⟩
  dsimp [radiusExponent, blockA]
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem caseB_uniform_margin (theta h m ell n : ℝ)
    (ht : ThetaWindow theta) (hr : HardRange theta h m)
    (he₀ : 0 ≤ ell) (he₁ : ell ≤ 1 / 100)
    (hn₀ : blockA h m ell ≤ n) (hn₁ : n ≤ blockB₂ h m) :
    1 / 1000 ≤ radiusExponent m n ∧
    1 / 1000 ≤ h - radiusExponent m n ∧
    1 / 1000 ≤ n - h ∧ 1 / 1000 ≤ m - n := by
  have hA := caseA_uniform_margin theta h m ell ht hr he₀ he₁
  rcases ht with ⟨ht₀, ht₁⟩
  rcases hr with ⟨hh₀, hh₁, hh₂, hm⟩
  dsimp [radiusExponent, blockA, blockB₂] at *
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- A power gap absorbs a fixed multiplicative factor at any base above 1. -/
theorem factor_rpow_le (T d a b B : ℝ) (hT : 1 ≤ T)
    (hgap : d ≤ b - a) (hB : B ≤ T ^ d) : B * T ^ a ≤ T ^ b := by
  calc
    B * T ^ a ≤ T ^ d * T ^ a := mul_le_mul_of_nonneg_right hB (by positivity)
    _ = T ^ (d + a) := (Real.rpow_add (by linarith) d a).symm
    _ ≤ T ^ b := Real.rpow_le_rpow_of_exponent_le hT (by linarith)

/-- Absorb ALL fixed constants at one threshold, uniform in h,m,n,r.
Here the actual N,R need only be comparable to the nominal powers. -/
theorem actual_separation_of_power_margins
    (D C T h m n r N R d : ℝ)
    (hD : 1 ≤ D) (_hC : 0 ≤ C) (hT : 1 ≤ T)
    (hN : Comparable D N (T ^ n)) (hR : Comparable D R (T ^ r))
    (hr : d ≤ r) (hrh : d ≤ h - r) (hhn : d ≤ n - h) (hnm : d ≤ m - n)
    (hlargeD : D ^ 2 ≤ T ^ d) (hlargeC : 64 * C * D ≤ T ^ d) :
    ExternalInterfaces.BlockSeparation D C (T ^ h) (T ^ m) N R := by
  have hDpos : 0 < D := by linarith
  rcases hN with ⟨hN₀, hN₁⟩
  rcases hR with ⟨hR₀, hR₁⟩
  have hpow : D ^ 2 ≤ T ^ r := hlargeD.trans (Real.rpow_le_rpow_of_exponent_le hT hr)
  refine ⟨?_, ?_, ?_, ?_⟩
  · have : D ≤ T ^ r / D := (le_div_iff₀ hDpos).mpr (by nlinarith)
    exact this.trans hR₀
  · calc
      D * R ≤ D * (D * T ^ r) := mul_le_mul_of_nonneg_left hR₁ hDpos.le
      _ = D ^ 2 * T ^ r := by ring
      _ ≤ T ^ h := factor_rpow_le T d r h (D ^ 2) hT hrh hlargeD
  · have hh := factor_rpow_le T d h n (64 * C * D) hT hhn hlargeC
    have : 64 * C * T ^ h ≤ T ^ n / D := (le_div_iff₀ hDpos).mpr (by nlinarith)
    exact this.trans hN₀
  · calc
      D * N ≤ D * (D * T ^ n) := mul_le_mul_of_nonneg_left hN₁ hDpos.le
      _ = D ^ 2 * T ^ n := by ring
      _ ≤ T ^ m := factor_rpow_le T d n m (D ^ 2) hT hnm hlargeD

theorem uniform_power_threshold (D C d : ℝ) (hd : 0 < d) :
    ∃ T₀ : ℝ, 1 ≤ T₀ ∧ ∀ T ≥ T₀, D ^ 2 ≤ T ^ d ∧ 64 * C * D ≤ T ^ d := by
  obtain ⟨T₁, hT₁⟩ := (tendsto_atTop_atTop.mp (tendsto_rpow_atTop hd))
    (max (D ^ 2) (64 * C * D))
  refine ⟨max 1 T₁, le_max_left _ _, fun T hT => ?_⟩
  have hh := hT₁ T ((le_max_right _ _).trans hT)
  exact ⟨(le_max_left _ _).trans hh, (le_max_right _ _).trans hh⟩

/-- This quantitative radius comparison includes both the block-construction
constant and the square root in R^2 ~ M^3/(NT). -/
theorem radius_comparable (D N N₀ R R₀ M T : ℝ)
    (hD : 1 ≤ D) (hN : 0 < N) (hN₀ : 0 < N₀)
    (hR : 0 < R) (hR₀ : 0 < R₀) (hT : 0 < T)
    (hn : Comparable D N N₀)
    (hr : Comparable D (R ^ 2) (M ^ 3 / (N * T)))
    (heq : R₀ ^ 2 * (N₀ * T) = M ^ 3) :
    Comparable D R R₀ := by
  have hDpos : 0 < D := by linarith
  have hn₀ := (div_le_iff₀ hDpos).mp hn.1
  have hr₀ := (div_le_iff₀ hDpos).mp hr.1
  have hr₀' := (div_le_iff₀ (mul_pos hN hT)).mp hr₀
  have hr₁ : R ^ 2 * (N * T) ≤ D * M ^ 3 := by
    have hh := (le_div_iff₀ (mul_pos hN hT)).mp
      (show R ^ 2 ≤ D * M ^ 3 / (N * T) by simpa only [mul_div_assoc] using hr.2)
    exact hh
  have hupper : R ≤ D * R₀ := by
    have hmul : R ^ 2 * (N₀ * T) ≤ D * (R ^ 2 * (N * T)) := by
      nlinarith [mul_le_mul_of_nonneg_left hn₀ (show 0 ≤ R ^ 2 * T by positivity)]
    have hmul' := mul_le_mul_of_nonneg_left hr₁ hDpos.le
    have hsquare : R ^ 2 ≤ (D * R₀) ^ 2 := by
      have hh : R ^ 2 * (N₀ * T) ≤ (D * R₀) ^ 2 * (N₀ * T) := by
        calc
          _ ≤ D * (R ^ 2 * (N * T)) := hmul
          _ ≤ D * (D * M ^ 3) := hmul'
          _ = (D * R₀) ^ 2 * (N₀ * T) := by rw [← heq]; ring
      exact (mul_le_mul_iff_left₀ (mul_pos hN₀ hT)).mp hh
    exact (sq_le_sq₀ hR.le (mul_pos hDpos hR₀).le).mp hsquare
  have hlower : R₀ ≤ R * D := by
    have hmul : D * R ^ 2 * (N * T) ≤ D ^ 2 * R ^ 2 * (N₀ * T) := by
      have hh := mul_le_mul_of_nonneg_left hn.2 (show 0 ≤ D * R ^ 2 * T by positivity)
      nlinarith
    have hsquare : R₀ ^ 2 ≤ (R * D) ^ 2 := by
      have hh : R₀ ^ 2 * (N₀ * T) ≤ (R * D) ^ 2 * (N₀ * T) := by
        calc
          _ = M ^ 3 := heq
          _ ≤ D * R ^ 2 * (N * T) := by nlinarith [hr₀']
          _ ≤ D ^ 2 * R ^ 2 * (N₀ * T) := hmul
          _ = (R * D) ^ 2 * (N₀ * T) := by ring
      exact (mul_le_mul_iff_left₀ (mul_pos hN₀ hT)).mp hh
    exact (sq_le_sq₀ hR₀.le (mul_pos hR hDpos).le).mp hsquare
  exact ⟨(div_le_iff₀ hDpos).mpr hlower, hupper⟩

end
end CircleDivisor.BlockSeparation
