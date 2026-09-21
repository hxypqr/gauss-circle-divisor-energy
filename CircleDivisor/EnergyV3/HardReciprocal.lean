import CircleDivisor.EnergyV3.ArithmeticInterface
import CircleDivisor.EnergyV3.CaseAssembly
import CircleDivisor.EnergyV3.ExternalArithmetic

/-! The complete difficult-range arithmetic application. This theorem assumes
the named internal first-spacing statement and the named external Li--Yang
input; all case selection, block admissibility, comparisons, losses, and
uniform thresholds between them and the actual weighted sum are proved. -/

namespace CircleDivisor.EnergyV3.HardReciprocal
noncomputable section
open CircleDivisor.Arithmetic CircleDivisor.ExternalInterfaces
open CircleDivisor.LogScale CaseAssembly ArithmeticInterface

theorem hard_reciprocal_fixed_moment (hspacing : FirstSpacingStatement) (hLY : LiYangInput)
    (q c C W ε : ℝ) (hq : 4 < q) (hqu : q ≤ 9/2)
    (hc : 0 < c) (hC : 2 ≤ C) (hcC : 1/c ≤ C) (hW : 0 < W) (hε : 0 < ε) :
    ∃ T₁ A₁ : ℝ, 2 ≤ T₁ ∧ 0 < A₁ ∧
      ∀ T : ℝ, T₁ ≤ T → ∀ h m : ℝ, HardRange theta h m → qHat (h-m)=q →
      ∀ F : ℝ → ℝ, PhaseControl c C F →
      ∀ g G : ℝ → ℂ, BVControl W g → BVControl W G →
        ‖reciprocalSum (T^h) (T^m) T F g G‖ ≤ A₁*T^h*T^(theta+ε) := by
  obtain ⟨B₀,D,M₀,T₀,A,hB₀,hD10,hM₀,hT₀,hA,hinput⟩ :=
    hLY q hq hqu c C W (ε/2) hc hC hcC hW (by linarith)
  have hD : 1 ≤ D := by linarith
  obtain ⟨B,hB,hmajor⟩ := spacingMajorized_of_firstSpacing hspacing q (ε/2) D hq hqu
    (by linarith) hD
  obtain ⟨TL,hTL⟩ := Filter.eventually_atTop.mp eventually_log_correction
  obtain ⟨TC,hTC1,hTC⟩ := CircleDivisor.BlockSeparation.uniform_power_threshold D C
    (1/1000) (by norm_num)
  obtain ⟨TE,hTE1,hTE⟩ := Construction.extra_standing_threshold D C (1/1000) (by norm_num)
  obtain ⟨TM,hTM⟩ := Filter.tendsto_atTop_atTop.mp
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<2/5)) M₀
  obtain ⟨TB,hTB⟩ := Filter.tendsto_atTop_atTop.mp
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<137/7312)) (1/B₀)
  refine ⟨max 2 (max T₀ (max TL (max TC (max TE (max TM TB))))), A*B,
    le_max_left _ _, mul_pos hA hB, ?_⟩
  intro T hT h m hr hqhat F hF g G hg hG
  simp only [max_le_iff] at hT
  rcases hT with ⟨hT2,hT0,hTL',hTC',hTE',hTM',hTB'⟩
  have hT1 : 1 < T := by linarith
  have ht : 0 < T := by linarith
  have hell := hTL T hTL'
  have hlarge := hTC T hTC'
  have hh : 0 ≤ h := by
    have h0 := hr.1
    norm_num [theta] at h0
    linarith
  have hm : 2/5 ≤ m := by
    have h0 := hard_m_lower theta h m hr
    norm_num [theta] at h0
    linarith
  have hM : M₀ ≤ T^m := (hTM T hTM').trans
    (Real.rpow_le_rpow_of_exponent_le hT1.le hm)
  have hsqrt : T^m ≤ Real.sqrt T := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hT1.le hr.2.2.2
  obtain ⟨b,n,hcase,hblock,hn,hmargin⟩ :=
    selected_case B₀ T h m hB₀ hT1 hr hell.1 hell.2 (hTB T hTB')
  obtain ⟨N,R,hNp,hRp,hNcmp,hRcmp,hresult⟩ :=
    hinput F hF g G hg hG (T^h) (T^m) T
      (Real.one_le_rpow hT1.le hh) hM hT0 hsqrt b hcase
  have hN : 0 < (N:ℝ) := by exact_mod_cast hNp
  have hNcmp' : Comparable D (N:ℝ) (T^n) := by rwa [hblock] at hNcmp
  have hRcmp' : Comparable D R (T^radiusExponent m n) :=
    CircleDivisor.BlockSeparation.radius_comparable D N (T^n) R (T^radiusExponent m n)
      (T^m) T hD hN (by positivity) hRp (by positivity) ht hNcmp' hRcmp
      (radius_power_identity T m n ht)
  have hsep : BlockSeparation D C (T^h) (T^m) N R :=
    CircleDivisor.BlockSeparation.actual_separation_of_power_margins D C T h m n
      (radiusExponent m n) N R (1/1000) hD (by linarith) hT1.le hNcmp' hRcmp'
      hmargin.1 hmargin.2.1 hmargin.2.2.1 hmargin.2.2.2.1 hlarge.1 hlarge.2
  have hNM : (N:ℝ) ≤ T^m := by
    have hs := hsep.N_small
    nlinarith
  have hR1 : 1 ≤ R := hD.trans hsep.R_large
  have hmajor' := hmajor T h m (exponent T (Real.log T)) n N R hT1 hr hell.1 hn
    hqhat hN hR1 hNM hNcmp'.1 hRcmp'.1
  have hexc := hTE T hTE'
  have hextra := Construction.extra_standing_of_margins hD (by linarith) hT1.le hh
    hN hRp hNcmp' hRcmp' hmargin.2.2.2.2.1 hmargin.2.2.2.2.2 hexc.1 hexc.2
  have hstanding : StandingConditions D C (T^h) (T^m) N R :=
    ⟨hsep,hextra.1,hextra.2⟩
  have hbound := hresult hstanding (B*T^(h+theta+ε/2)) (by positivity) hmajor'
  have heq : A*T^(ε/2)*(B*T^(h+theta+ε/2)) = (A*B)*T^h*T^(theta+ε) := by
    have he : T^(ε/2)*T^(h+theta+ε/2) = T^h*T^(theta+ε) := by
      rw [← Real.rpow_add ht, ← Real.rpow_add ht]
      congr 1
      ring
    calc
      _ = (A*B)*(T^(ε/2)*T^(h+theta+ε/2)) := by ring
      _ = _ := by rw [he]; ring
  exact hbound.trans_eq heq

/-- One constant and threshold for the whole hard range. Only a maximum of
four already obtained constants is taken. -/
theorem hard_reciprocal_uniform (hspacing : FirstSpacingStatement) (hLY : LiYangInput)
    (c C W ε : ℝ) (hc : 0 < c) (hC : 2 ≤ C) (hcC : 1/c ≤ C)
    (hW : 0 < W) (hε : 0 < ε) :
    ∃ T₁ A₁ : ℝ, 2 ≤ T₁ ∧ 0 < A₁ ∧
      ∀ T : ℝ, T₁ ≤ T → ∀ h m : ℝ, HardRange theta h m →
      ∀ F : ℝ → ℝ, PhaseControl c C F →
      ∀ g G : ℝ → ℂ, BVControl W g → BVControl W G →
        ‖reciprocalSum (T^h) (T^m) T F g G‖ ≤ A₁*T^h*T^(theta+ε) := by
  obtain ⟨T1,A1,hT1,hA1,hb1⟩ := hard_reciprocal_fixed_moment hspacing hLY
    (201/50) c C W ε (by norm_num) (by norm_num) hc hC hcC hW hε
  obtain ⟨T2,A2,hT2,hA2,hb2⟩ := hard_reciprocal_fixed_moment hspacing hLY
    (17/4) c C W ε (by norm_num) (by norm_num) hc hC hcC hW hε
  obtain ⟨T3,A3,hT3,hA3,hb3⟩ := hard_reciprocal_fixed_moment hspacing hLY
    (22/5) c C W ε (by norm_num) (by norm_num) hc hC hcC hW hε
  obtain ⟨T4,A4,hT4,hA4,hb4⟩ := hard_reciprocal_fixed_moment hspacing hLY
    (9/2) c C W ε (by norm_num) (by norm_num) hc hC hcC hW hε
  let A := max A1 (max A2 (max A3 A4))
  have hAa1 : A1 ≤ A := le_max_left _ _
  have hAa2 : A2 ≤ A := (le_max_left _ _).trans (le_max_right _ _)
  have hAa3 : A3 ≤ A := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hAa4 : A4 ≤ A := (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  refine ⟨max T1 (max T2 (max T3 T4)), A, hT1.trans (le_max_left _ _),
    hA1.trans_le hAa1, ?_⟩
  intro T hT h m hr F hF g G hg hG
  simp only [max_le_iff] at hT
  have ht : 0 < T := by linarith [hT.1]
  have hmono : ∀ A' : ℝ, A' ≤ A → A'*T^h*T^(theta+ε) ≤ A*T^h*T^(theta+ε) := by
    intro A' hA'
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hA' (by positivity)) (by positivity)
  have hmem := qHat_mem (h-m)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with hq | hq | hq | hq
  · exact (hb1 T hT.1 h m hr hq F hF g G hg hG).trans (hmono A1 hAa1)
  · exact (hb2 T hT.2.1 h m hr hq F hF g G hg hG).trans (hmono A2 hAa2)
  · exact (hb3 T hT.2.2.1 h m hr hq F hF g G hg hG).trans (hmono A3 hAa3)
  · exact (hb4 T hT.2.2.2 h m hr hq F hF g G hg hG).trans (hmono A4 hAa4)

end
end CircleDivisor.EnergyV3.HardReciprocal
