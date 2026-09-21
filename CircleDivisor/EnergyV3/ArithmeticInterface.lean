import CircleDivisor.EnergyV3.Statements
import CircleDivisor.EnergyV3.SpacingTransfer

/-! Complete substitution of the revised (internal) first-spacing statement
into the Li--Yang majorant. It includes the auxiliary P-loss and actual
integer parameter comparisons. `FirstSpacingStatement` is deliberately a
named premise here, to be supplied by the internal analytic branch. -/

namespace CircleDivisor.EnergyV3.ArithmeticInterface
noncomputable section
open CircleDivisor.Arithmetic CircleDivisor.ExternalInterfaces
open SpacingTransfer

theorem spacing_scale_bounds {D H M N R Q T η : ℝ} {K L : ℕ}
    (hD : 1 ≤ D) (hH : 0 < H) (hM : 0 < M) (hN : 0 < N)
    (hR : 1 ≤ R) (hQ : 0 < Q) (hQH : Q ≤ 3*H)
    (hHM : H ≤ M) (hNM : N ≤ M) (hMT : M^2 ≤ T)
    (p : SpacingParameters D H N R Q K L η) :
    (K:ℝ) ≤ 3*D*T ∧ (L:ℝ) ≤ 3*D*T ∧
    (K:ℝ)*L ≤ (9*D^2)*T^2 := by
  have hDp : 0 < D := by linarith
  have hRp : 0 < R := by linarith
  have hR2 : 1 ≤ R^2 := by nlinarith
  have hQT : Q ≤ 3*M := by linarith
  have hmono : ∀ u : ℝ, 0 ≤ u → u ≤ M → D*(u*Q/R^2) ≤ 3*D*T := by
    intro u hu huM
    have hd : u*Q/R^2 ≤ u*Q := div_le_self (by positivity) hR2
    have hm : u*Q ≤ 3*M^2 := by nlinarith [mul_le_mul huM hQT hQ.le hM.le]
    nlinarith
  have hk := p.K_comparable.2.trans (hmono N hN.le hNM)
  have hl := p.L_comparable.2.trans (hmono H hH.le hHM)
  refine ⟨hk,hl,?_⟩
  have ht : 0 ≤ T := (sq_nonneg M).trans hMT
  have hp := mul_le_mul hk hl (show 0 ≤ (L:ℝ) by positivity) (by positivity : 0 ≤ 3*D*T)
  nlinarith

/-- Every fixed q has one majorant constant, independent of T,H,M and of
all denominator parameters. The q is subsequently selected from four values. -/
theorem spacingMajorized_of_firstSpacing (hspacing : FirstSpacingStatement)
    (q ε D : ℝ) (hq : 4 < q) (hqu : q ≤ 9/2) (hε : 0 < ε) (hD : 1 ≤ D) :
    ∃ B : ℝ, 0 < B ∧ ∀ T h m ell n N R : ℝ,
      1 < T → HardRange theta h m → 0 ≤ ell → blockA h m ell ≤ n →
      qHat (h-m) = q → 0 < N → 1 ≤ R → N ≤ T^m →
      T^n/D ≤ N → T^radiusExponent m n/D ≤ R →
      spacingMajorized D (T^h) (T^m) N R q (B*T^(h+theta+ε)) := by
  have hqp : 0 < q := by linarith
  have hDp : 0 < D := by linarith
  let δ := ε*q/2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨Cs,hCs,hsp⟩ := hspacing q hq hqu δ hδ
  let C₀ := Cs * (9*D^2)^δ
  let B := 4*(C₀*D^6)^(1/q)*D^2
  have hC₀ : 0 < C₀ := by dsimp [C₀]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨B,hB,?_⟩
  intro T h m ell n N R hT hr hell hn hqhat hN hR hNM hNl hRl
  have ht : 0 < T := by linarith
  have hRp : 0 < R := by linarith
  intro Q hQ K L η p a ha
  have hQp : 0 < Q := hRp.trans_le hQ.1
  have hHM : T^h ≤ T^m := Real.rpow_le_rpow_of_exponent_le hT.le (by
    have hh := hr.2.1
    have hθ : 0 < theta := by norm_num [theta]
    linarith)
  have hMT : (T^m)^2 ≤ T := by
    rw [← Real.rpow_mul_natCast ht.le]
    calc
      _ ≤ T^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le hT.le (by norm_num; linarith [hr.2.2.2])
      _ = T := Real.rpow_one _
  have hsc := spacing_scale_bounds hD (by positivity) (by positivity) hN hR hQp
    hQ.2.1 hHM hNM hMT p
  have hP : ((K:ℝ)*L)^δ ≤ (9*D^2)^δ * T^(2*δ) := by
    calc
      _ ≤ ((9*D^2)*T^2)^δ := Real.rpow_le_rpow (by positivity) hsc.2.2 hδ.le
      _ = _ := by
        rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast_mul ht.le]
        norm_num
  have hmoment : coneMoment K L q a ≤ (C₀*T^(2*δ)) * Arithmetic.fourTerm K L q := by
    have hh := hsp K L (by exact_mod_cast p.L_one) (by exact_mod_cast p.L_le_K) a ha
    have hf : 0 ≤ Arithmetic.fourTerm K L q := by unfold Arithmetic.fourTerm; positivity
    have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hP hCs.le) hf
    dsimp [C₀]
    nlinarith
  have hh := actual_moment_contribution_bound hD hT hN hRp hNl hRl hr hell hn
    hQ.1 (show 0 ≤ C₀*T^(2*δ) by positivity) p a (by simpa [hqhat] using hmoment)
  rw [hqhat] at hh
  have he : 4*((C₀*T^(2*δ))*D^6)^(1/q)*D^2*T^(h+theta) = B*T^(h+theta+ε) := by
    rw [show C₀*T^(2*δ)*D^6 = (C₀*D^6)*T^(2*δ) by ring,
      Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul ht.le]
    have hed : 2*δ*(1/q)=ε := by dsimp [δ]; field_simp <;> ring
    rw [hed]
    simp only [Real.rpow_add ht]
    dsimp [B]
    ring
  exact hh.trans_eq he

end
end CircleDivisor.EnergyV3.ArithmeticInterface
