import CircleDivisor.EnergyV3.PairedCount

namespace CircleDivisor.EnergyV3.PairedCount
open Finset CircleDivisor.SpacingCount
noncomputable section

theorem count_quadruples_of_divisor_estimate (K L W V : ℕ)
    (hL : 1 ≤ L) (hW : 1 ≤ W) (hV : 1 ≤ V)
    (ε C : ℝ) (hε : 0 ≤ ε) (hC : 1 ≤ C) (hdiv : NaturalDivisorEstimate ε C)
    (S : Finset Quadruple) (hS : ∀ x ∈ S, Admissible K L W V x) :
    (S.card : ℝ) ≤ 18 * K * (1 + 2 * C * (4 * (L : ℝ) * W) ^ ε) *
      ((W : ℝ) ^ 2 * (L : ℝ) ^ 2 + V * W * L) := by
  let B : ℝ := 4 * L * W
  let R : ℝ := 2 * C * B ^ ε
  let D : ℕ := Nat.ceil R
  have hB : 0 < B := by
    have : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
    have : (0 : ℝ) < W := by exact_mod_cast (show 0 < W by omega)
    dsimp [B]; positivity
  have hR : 0 < R := by dsimp [R]; positivity
  have hD : DivisorBound L (2 * W) D := by
    intro n hn habs
    have hh := hdiv n.natAbs (Int.natAbs_pos.mpr hn)
    have hni : (n.natAbs : ℤ) ≤ 4 * (L : ℤ) * W := by
      rw [Int.natCast_natAbs]
      push_cast at habs
      nlinarith
    have hnr : (n.natAbs : ℝ) ≤ B := by dsimp [B]; exact_mod_cast hni
    have hpow := Real.rpow_le_rpow (Nat.cast_nonneg n.natAbs) hnr hε
    have hc : ((divisorsIn L n).card : ℝ) ≤ 2 * (n.natAbs.divisors.card : ℝ) := by
      exact_mod_cast card_divisorsIn_le L n hn
    have hbound : ((divisorsIn L n).card : ℝ) ≤ R := by dsimp [R]; nlinarith
    exact_mod_cast hbound.trans (Nat.le_ceil R)
  have hcount : (S.card : ℝ) ≤ 18 * K * D *
      ((W : ℝ) ^ 2 * (L : ℝ) ^ 2 + V * W * L) := by
    exact_mod_cast count_quadruples K L W V D hL hW hV S hS hD
  have hceil : (D : ℝ) ≤ 1 + R := by
    have := Nat.ceil_lt_add_one (le_of_lt hR)
    dsimp [D]; linarith
  calc
    _ ≤ _ := hcount
    _ ≤ 18 * K * (1 + R) * ((W : ℝ) ^ 2 * (L : ℝ) ^ 2 + V * W * L) := by gcongr
    _ = _ := rfl

structure RealAdmissible (K L W V : ℝ) (x : Quadruple) : Prop where
  base_mem : (x.k4 : ℝ) ∈ Set.Ico K (2 * K)
  l1_mem : (x.l1 : ℝ) ∈ Set.Ico L (2 * L)
  l2_mem : (x.l2 : ℝ) ∈ Set.Ico L (2 * L)
  l3_mem : (x.l3 : ℝ) ∈ Set.Ico L (2 * L)
  first : firstEquation x
  second : secondEquation x
  d1_bound : |((x.k1 - x.k2 : ℤ) : ℝ)| ≤ W
  d2_bound : |((x.k3 - x.k4 : ℤ) : ℝ)| ≤ W
  u_bound : |((x.k2 - x.k4 : ℤ) : ℝ)| ≤ V
  d1_ne : x.k1 ≠ x.k2
  d2_ne : x.k3 ≠ x.k4

theorem real_interval_to_ceiling (X : ℝ) (hX : 1 ≤ X) (k : ℤ)
    (hk : (k : ℝ) ∈ Set.Ico X (2 * X)) : k ∈ baseSet (Nat.ceil X) := by
  simp only [baseSet, mem_Ico]
  constructor
  · rw [Int.natCast_ceil_eq_ceil (by linarith : 0 ≤ X)]
    exact Int.ceil_le.mpr hk.1
  · have hx := Nat.le_ceil X
    have hu : (k : ℝ) < 2 * (Nat.ceil X : ℝ) := by linarith [hk.2]
    exact_mod_cast hu

theorem RealAdmissible.ceiling {K L W V : ℝ} {x : Quadruple}
    (h : RealAdmissible K L W V x) (hK : 1 ≤ K) (hL : 1 ≤ L) :
    Admissible (Nat.ceil K) (Nat.ceil L) (Nat.ceil W) (Nat.ceil V) x := by
  refine ⟨real_interval_to_ceiling K hK x.k4 h.base_mem,
    real_interval_to_ceiling L hL x.l1 h.l1_mem,
    real_interval_to_ceiling L hL x.l2 h.l2_mem,
    real_interval_to_ceiling L hL x.l3 h.l3_mem, h.first, h.second,
    ?_, ?_, ?_, h.d1_ne, h.d2_ne⟩
  · exact_mod_cast h.d1_bound.trans (Nat.le_ceil W)
  · exact_mod_cast h.d2_bound.trans (Nat.le_ceil W)
  · exact_mod_cast h.u_bound.trans (Nat.le_ceil V)

theorem ceil_le_twice (X : ℝ) (hX : 1 ≤ X) : (Nat.ceil X : ℝ) ≤ 2 * X := by
  have := Nat.ceil_lt_add_one (by linarith : 0 ≤ X)
  linarith

theorem count_real_parameters (K L W V : ℝ) (hK : 1 ≤ K) (hL : 1 ≤ L)
    (hW : 1 ≤ W) (hV : 1 ≤ V)
    (ε C : ℝ) (hε : 0 ≤ ε) (hC : 1 ≤ C) (hdiv : NaturalDivisorEstimate ε C)
    (S : Finset Quadruple) (hS : ∀ x ∈ S, RealAdmissible K L W V x) :
    (S.card : ℝ) ≤ 576 * K * (1 + 2 * C * (16 * L * W) ^ ε) *
      (W ^ 2 * L ^ 2 + V * W * L) := by
  have hLc : 1 ≤ Nat.ceil L := Nat.one_le_ceil_iff.mpr (by linarith)
  have hWc : 1 ≤ Nat.ceil W := Nat.one_le_ceil_iff.mpr (by linarith)
  have hVc : 1 ≤ Nat.ceil V := Nat.one_le_ceil_iff.mpr (by linarith)
  have hc := count_quadruples_of_divisor_estimate (Nat.ceil K) (Nat.ceil L)
    (Nat.ceil W) (Nat.ceil V) hLc hWc hVc ε C hε hC hdiv S
    (fun x hx => (hS x hx).ceiling hK hL)
  have hk := ceil_le_twice K hK
  have hl := ceil_le_twice L hL
  have hw := ceil_le_twice W hW
  have hv := ceil_le_twice V hV
  have hb : 4 * (Nat.ceil L : ℝ) * Nat.ceil W ≤ 16 * L * W := by
    calc
      _ ≤ 4 * (2 * L) * (2 * W) := by gcongr
      _ = _ := by ring
  have hp := Real.rpow_le_rpow (by positivity) hb hε
  calc
    _ ≤ _ := hc
    _ ≤ 18 * (2 * K) * (1 + 2 * C * (16 * L * W) ^ ε) *
        ((2 * W) ^ 2 * (2 * L) ^ 2 + (2 * V) * (2 * W) * (2 * L)) := by gcongr
    _ ≤ _ := by
      have hpos : 0 ≤ K * (1 + 2 * C * (16 * L * W) ^ ε) * (V * W * L) := by positivity
      nlinarith [hpos]

/-- The precise two-scale shape, for arbitrary subsets and real parameters.
`C` is solely the constant in the classical divisor estimate. -/
theorem paired_count_real (K L W V A : ℝ) (hK : 1 ≤ K) (hL : 1 ≤ L)
    (hW : 1 ≤ W) (hV : 1 ≤ V) (hA : 1 ≤ A) (hWK : W ≤ A * K)
    (ε C : ℝ) (hε : 0 ≤ ε) (hC : 1 ≤ C) (hdiv : NaturalDivisorEstimate ε C)
    (S : Finset Quadruple) (hS : ∀ x ∈ S, RealAdmissible K L W V x) :
    (S.card : ℝ) ≤ (576 * (1 + 2 * C * (16 * A) ^ ε)) *
      (K * L) ^ ε * K * (W ^ 2 * L ^ 2 + V * W * L) := by
  have hmain := count_real_parameters K L W V hK hL hW hV ε C hε hC hdiv S hS
  have hP : 1 ≤ K * L := by nlinarith
  have hp : 1 ≤ (K * L) ^ ε := Real.one_le_rpow hP hε
  have hbase : 16 * L * W ≤ (16 * A) * (K * L) := by nlinarith
  have hpower : (16 * L * W) ^ ε ≤ (16 * A) ^ ε * (K * L) ^ ε := by
    rw [← Real.mul_rpow (by positivity : 0 ≤ 16 * A) (by positivity : 0 ≤ K * L)]
    exact Real.rpow_le_rpow (by positivity) hbase hε
  have hbracket : 1 + 2 * C * (16 * L * W) ^ ε ≤
      (1 + 2 * C * (16 * A) ^ ε) * (K * L) ^ ε := by nlinarith
  calc
    _ ≤ _ := hmain
    _ ≤ 576 * K * ((1 + 2 * C * (16 * A) ^ ε) * (K * L) ^ ε) *
        (W ^ 2 * L ^ 2 + V * W * L) := by gcongr
    _ = _ := by ring

end
end CircleDivisor.EnergyV3.PairedCount
