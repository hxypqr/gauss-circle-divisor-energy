import CircleDivisor.EnergyV3.ShellSummation

/-! Local density: actual dual-envelope distance, integer neighbors, and
finite decaying-kernel sums. No count or shell estimate is postulated. -/

namespace CircleDivisor.EnergyV3.DensitySums
noncomputable section
open scoped BigOperators
open Finset
abbrev Point := ℤ × ℤ

def distance (K L s t₀ : ℝ) (p q : Point) : ℝ :=
  ‖AdaptedMetric.dualCoordinates (K * L) s t₀
    (ConeGeometry.frequency K L p.1 p.2 - ConeGeometry.frequency K L q.1 q.2)‖

theorem cross_decay_sum (S : Finset Point) (center : Point)
    (K L s t₀ : ℝ) (hK : 0 < K) (hL : 0 < L) (hs : 0 < s) (hs1 : s ≤ 1)
    (ht0 : 0 ≤ t₀) (ht2 : t₀ ≤ 2)
    (hcenter : K ≤ (center.1 : ℝ) ∧ (center.1 : ℝ) < 2*K)
    (hangle : |Real.sqrt ((center.1 : ℝ) / K) - t₀| ≤ s)
    (hS : ∀ p ∈ S, K ≤ (p.1 : ℝ) ∧ (p.1 : ℝ) < 2*K ∧ L ≤ (p.2 : ℝ)) :
    ∑ p ∈ S, ((1 + distance K L s t₀ p center) ^ 8)⁻¹ ≤
      (256 * (64 / 63 : ℝ)) * 5832 * (1 + 1/(K*s^2)) * (1 + 1/(L*s)) := by
  apply ShellSummation.finite_decay_sum S (fun p => distance K L s t₀ p center)
    (1/(K*s^2)) (1/(L*s)) 5832 (by positivity) (by positivity) (by norm_num)
    (fun _ _ => norm_nonneg _)
  intro j
  have hh := NeighborCount.actual_dual_neighbor_count
    (S.filter (fun p => distance K L s t₀ p center ≤ 2 ^ j)) center K L s (2 ^ j) t₀
    hK hL hs hs1 ht0 ht2 (by positivity) hcenter hangle
    (fun p hp => hS p (mem_filter.mp hp).1) (fun p hp => (mem_filter.mp hp).2)
  simpa only [div_eq_mul_inv, one_mul] using hh

theorem coarse_card (S : Finset Point) (K L s t₀ : ℝ) (hK : 0 < K) (hL : 1 ≤ L)
    (hs : 0 < s) (hsK : 1 ≤ s * K)
    (hS : ∀ p ∈ S, K ≤ (p.1 : ℝ) ∧ (p.1 : ℝ) < 2*K ∧
      L ≤ (p.2 : ℝ) ∧ (p.2 : ℝ) < 2*L)
    (hangle : ∀ p ∈ S, |Real.sqrt ((p.1 : ℝ) / K) - t₀| ≤ s) :
    (S.card : ℝ) ≤ 162 * (s * K * L) := by
  rcases S.eq_empty_or_nonempty with he | ⟨center, hcenter⟩
  · simp [he]
    positivity
  have hL0 : 0 < L := by linarith
  have hh := NeighborCount.integer_neighbor_count S center (A := L) (B := 8 * K * s)
    hL0.le (by positivity) (by
      intro p hp
      constructor
      · rw [Int.cast_sub, abs_le]
        constructor <;> linarith [(hS p hp).2.2.1, (hS p hp).2.2.2,
          (hS center hcenter).2.2.1, (hS center hcenter).2.2.2]
      · have ht : |Real.sqrt ((p.1 : ℝ)/K) - Real.sqrt ((center.1 : ℝ)/K)| ≤ 2*s := by
          have hh := abs_sub_le (Real.sqrt ((p.1 : ℝ)/K)) t₀ (Real.sqrt ((center.1 : ℝ)/K))
          rw [abs_sub_comm t₀] at hh
          linarith [hangle p hp, hangle center hcenter]
        have hk := NeighborCount.index_distance_of_parameter_distance hK (hS p hp).1
          (hS p hp).2.1 (hS center hcenter).1 (hS center hcenter).2.1 ht
        simpa only [Int.cast_sub, show 4 * K * (2 * s) = 8 * K * s by ring] using hk)
  calc
    _ ≤ 9 * (1 + L) * (1 + 8 * K * s) := hh
    _ ≤ 9 * (2 * L) * (9 * K * s) := by gcongr <;> nlinarith
    _ = _ := by ring

theorem all_pairs_decay_sum (S : Finset Point) (K L s t₀ : ℝ)
    (hK : 0 < K) (hL : 1 ≤ L) (hs : 0 < s) (hs1 : s ≤ 1) (hsK : 1 ≤ s*K)
    (ht0 : 0 ≤ t₀) (ht2 : t₀ ≤ 2)
    (hS : ∀ p ∈ S, K ≤ (p.1 : ℝ) ∧ (p.1 : ℝ) < 2*K ∧
      L ≤ (p.2 : ℝ) ∧ (p.2 : ℝ) < 2*L)
    (hangle : ∀ p ∈ S, |Real.sqrt ((p.1 : ℝ) / K) - t₀| ≤ s) :
    ∑ q ∈ S, ∑ p ∈ S, ((1 + distance K L s t₀ p q) ^ 8)⁻¹ ≤
      (162 * (256 * (64 / 63 : ℝ)) * 5832) *
        (s*K*L*(1+1/(K*s^2))*(1+1/(L*s))) := by
  have hL0 : 0 < L := by linarith
  have hrow (q : Point) (hq : q ∈ S) := cross_decay_sum S q K L s t₀ hK hL0 hs hs1 ht0 ht2
    ⟨(hS q hq).1, (hS q hq).2.1⟩ (hangle q hq)
    (fun p hp => ⟨(hS p hp).1, (hS p hp).2.1, (hS p hp).2.2.1⟩)
  have hcard := coarse_card S K L s t₀ hK hL hs hsK hS hangle
  calc
    _ ≤ ∑ q ∈ S, (256 * (64 / 63 : ℝ)) * 5832 * (1+1/(K*s^2)) * (1+1/(L*s)) :=
      sum_le_sum hrow
    _ = S.card * ((256 * (64 / 63 : ℝ)) * 5832 * (1+1/(K*s^2)) * (1+1/(L*s))) := by simp
    _ ≤ (162 * (s*K*L)) * ((256 * (64 / 63 : ℝ)) * 5832 * (1+1/(K*s^2)) * (1+1/(L*s))) := by
      gcongr
    _ = _ := by ring

theorem radial_distance_le (p q : Point) (K L s t₀ : ℝ)
    (hK : 0 < K) (hL : 0 < L) (hs : 0 < s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t₀) (ht2 : t₀ ≤ 2) :
    |((p.2 - q.2 : ℤ) : ℝ)| ≤ 9 * distance K L s t₀ p q / (K*s^2) := by
  have hm := (AdaptedMetric.transpose_controls_adapted (mul_pos hK hL) hs hs1 ht0 ht2
    (ConeGeometry.frequency K L p.1 p.2 - ConeGeometry.frequency K L q.1 q.2)).1
  change K*L*s^2*|(p.2 : ℝ)/L - (q.2 : ℝ)/L| ≤ 9 * distance K L s t₀ p q at hm
  rw [← sub_div, abs_div, abs_of_pos hL] at hm
  have he : K*L*s^2*(|(p.2 : ℝ)-(q.2 : ℝ)|/L) = K*s^2*|(p.2 : ℝ)-(q.2 : ℝ)| := by field_simp
  rw [he] at hm
  apply (le_div_iff₀ (by positivity : 0 < K*s^2)).mpr
  simpa only [Int.cast_sub, mul_comm (K*s^2)] using hm

theorem same_ray_decay_sum (S : Finset Point) (center : Point)
    (K L s t₀ : ℝ) (hK : 0 < K) (hL : 0 < L) (hs : 0 < s) (hs1 : s ≤ 1)
    (ht0 : 0 ≤ t₀) (ht2 : t₀ ≤ 2) (hS : ∀ p ∈ S, p.1 = center.1) :
    ∑ p ∈ S, ((1 + distance K L s t₀ p center) ^ 8)⁻¹ ≤
      (256 * (64 / 63 : ℝ)) * 27 * (1 + 1/(K*s^2)) := by
  have hh := ShellSummation.finite_decay_sum S (fun p => distance K L s t₀ p center)
    (1/(K*s^2)) 0 27 (by positivity) (by norm_num) (by norm_num)
    (fun _ _ => norm_nonneg _) (by
      intro j
      have hc := NeighborCount.same_ray_neighbor_count
        (S.filter (fun p => distance K L s t₀ p center ≤ 2^j)) center
        (A := 9 * 2^j / (K*s^2)) (by positivity) (by
          intro p hp
          obtain ⟨hp, hd⟩ := mem_filter.mp hp
          refine ⟨hS p hp, (radial_distance_le p center K L s t₀ hK hL hs hs1 ht0 ht2).trans ?_⟩
          gcongr)
      have hnn : 0 ≤ (2:ℝ)^j/(K*s^2) := by positivity
      simp only [mul_zero, add_zero, mul_one]
      have he : 9 * (2:ℝ)^j/(K*s^2) = 9 * ((2:ℝ)^j * (1/(K*s^2))) := by ring
      rw [he] at hc
      linarith)
  simpa only [mul_zero, add_zero, mul_one] using hh

theorem wide_dual_neighbor_count (S : Finset Point) (center : Point)
    (K L s t₀ A N : ℝ) (hK : 0 < K) (hL : 0 < L) (hs : 0 < s) (hs1 : s ≤ 1)
    (ht0 : 0 ≤ t₀) (ht2 : t₀ ≤ 2) (hA : 1 ≤ A) (hN : 0 ≤ N)
    (hcenter : K ≤ (center.1 : ℝ) ∧ (center.1 : ℝ) < 2*K)
    (hangle : |Real.sqrt ((center.1 : ℝ) / K) - t₀| ≤ A*s)
    (hS : ∀ p ∈ S, K ≤ (p.1 : ℝ) ∧ (p.1 : ℝ) < 2*K ∧ L ≤ (p.2 : ℝ))
    (hmetric : ∀ p ∈ S, distance K L s t₀ p center ≤ N) :
    (S.card : ℝ) ≤ 5832*A*(1+N/(K*s^2))*(1+N/(L*s)) := by
  have hA0 : 0 < A := by linarith
  have hsep (p : Point) (hp : p ∈ S) :
      |((p.2-center.2 : ℤ) : ℝ)| ≤ 9*N/(K*s^2) ∧
      |((p.1-center.1 : ℤ) : ℝ)| ≤ 72*A*N/(L*s) := by
    have hm := AdaptedMetric.transpose_controls_adapted (mul_pos hK hL) hs hs1 ht0 ht2
      (ConeGeometry.frequency K L p.1 p.2 - ConeGeometry.frequency K L center.1 center.2)
    have hdist : ‖AdaptedMetric.dualCoordinates (K*L) s t₀
        (ConeGeometry.frequency K L p.1 p.2 - ConeGeometry.frequency K L center.1 center.2)‖ ≤ N := hmetric p hp
    have hz : |ConeGeometry.adapted t₀
        (ConeGeometry.frequency K L p.1 p.2 - ConeGeometry.frequency K L center.1 center.2) 0| ≤
        (9*A^2*N)/(K*L*(A*s)^2) := by
      have hh : (9*A^2*N)/(K*L*(A*s)^2) = 9*N/(K*L*s^2) := by field_simp
      rw [hh]
      apply (le_div_iff₀ (by positivity : 0 < K*L*s^2)).mpr
      nlinarith [hm.1, hdist]
    have ho : |ConeGeometry.adapted t₀
        (ConeGeometry.frequency K L p.1 p.2 - ConeGeometry.frequency K L center.1 center.2) 1| ≤
        (9*A^2*N)/(K*L*(A*s)) := by
      have hh : (9*A^2*N)/(K*L*(A*s)) = 9*A*N/(K*L*s) := by field_simp
      rw [hh]
      apply (le_div_iff₀ (by positivity : 0 < K*L*s)).mpr
      nlinarith [hm.2.1, hdist, mul_nonneg (show 0 ≤ A-1 by linarith) hN]
    have hh := NeighborCount.actual_frequency_neighbor_separation hK hL (mul_pos hA0 hs)
      (hS p hp).1 (hS p hp).2.1 hcenter.1 hcenter.2 (hS p hp).2.2 hangle hz ho
    have he0 : (9*A^2*N)/(K*(A*s)^2) = 9*N/(K*s^2) := by field_simp
    have he1 : 8*(9*A^2*N)/(L*(A*s)) = 72*A*N/(L*s) := by field_simp; ring
    simpa only [Int.cast_sub, he0, he1] using hh
  have hc := NeighborCount.integer_neighbor_count S center
    (A := 9*N/(K*s^2)) (B := 72*A*N/(L*s)) (by positivity) (by positivity) hsep
  have he0 : 9*N/(K*s^2) = 9*(N/(K*s^2)) := by ring
  have he1 : 72*A*N/(L*s) = 72*A*(N/(L*s)) := by ring
  rw [he0, he1] at hc
  calc
    _ ≤ 9*(1+9*(N/(K*s^2)))*(1+72*A*(N/(L*s))) := hc
    _ ≤ 9*(9*(1+N/(K*s^2)))*(72*A*(1+N/(L*s))) := by gcongr <;> nlinarith
    _ = _ := by ring

theorem wide_cross_decay_sum (S : Finset Point) (center : Point)
    (K L s t₀ A : ℝ) (hK : 0 < K) (hL : 0 < L) (hs : 0 < s) (hs1 : s ≤ 1)
    (ht0 : 0 ≤ t₀) (ht2 : t₀ ≤ 2) (hA : 1 ≤ A)
    (hcenter : K ≤ (center.1 : ℝ) ∧ (center.1 : ℝ) < 2*K)
    (hangle : |Real.sqrt ((center.1 : ℝ) / K) - t₀| ≤ A*s)
    (hS : ∀ p ∈ S, K ≤ (p.1 : ℝ) ∧ (p.1 : ℝ) < 2*K ∧ L ≤ (p.2 : ℝ)) :
    ∑ p ∈ S, ((1 + distance K L s t₀ p center) ^ 8)⁻¹ ≤
      (256 * (64 / 63 : ℝ)) * (5832*A) * (1 + 1/(K*s^2)) * (1 + 1/(L*s)) := by
  have hA0 : 0 < A := by linarith
  apply ShellSummation.finite_decay_sum S (fun p => distance K L s t₀ p center)
    (1/(K*s^2)) (1/(L*s)) (5832*A) (by positivity) (by positivity) (by positivity)
    (fun _ _ => norm_nonneg _)
  intro j
  have hh := wide_dual_neighbor_count
    (S.filter (fun p => distance K L s t₀ p center ≤ 2 ^ j)) center K L s t₀ A (2 ^ j)
    hK hL hs hs1 ht0 ht2 hA (by positivity) hcenter hangle
    (fun p hp => hS p (mem_filter.mp hp).1) (fun p hp => (mem_filter.mp hp).2)
  simpa only [div_eq_mul_inv, one_mul] using hh

theorem wide_coarse_card (S : Finset Point) (K L s t₀ A : ℝ) (hK : 0 < K)
    (hL : 1 ≤ L) (hs : 0 < s) (hsK : 1 ≤ s*K) (hA : 1 ≤ A)
    (hS : ∀ p ∈ S, K ≤ (p.1 : ℝ) ∧ (p.1 : ℝ) < 2*K ∧
      L ≤ (p.2 : ℝ) ∧ (p.2 : ℝ) < 2*L)
    (hangle : ∀ p ∈ S, |Real.sqrt ((p.1 : ℝ)/K)-t₀| ≤ A*s) :
    (S.card : ℝ) ≤ 162*A*(s*K*L) := by
  have hA0 : 0 < A := by linarith
  have hh := coarse_card S K L (A*s) t₀ hK hL (mul_pos hA0 hs)
    (by nlinarith) hS hangle
  nlinarith

theorem wide_all_pairs_decay_sum (S : Finset Point) (K L s t₀ A : ℝ)
    (hK : 0 < K) (hL : 1 ≤ L) (hs : 0 < s) (hs1 : s ≤ 1) (hsK : 1 ≤ s*K)
    (ht0 : 0 ≤ t₀) (ht2 : t₀ ≤ 2) (hA : 1 ≤ A)
    (hS : ∀ p ∈ S, K ≤ (p.1 : ℝ) ∧ (p.1 : ℝ) < 2*K ∧
      L ≤ (p.2 : ℝ) ∧ (p.2 : ℝ) < 2*L)
    (hangle : ∀ p ∈ S, |Real.sqrt ((p.1 : ℝ)/K)-t₀| ≤ A*s) :
    ∑ q ∈ S, ∑ p ∈ S, ((1+distance K L s t₀ p q)^8)⁻¹ ≤
      (162*(256*(64/63 : ℝ))*5832*A^2)*
        (s*K*L*(1+1/(K*s^2))*(1+1/(L*s))) := by
  have hA0 : 0 < A := by linarith
  have hL0 : 0 < L := by linarith
  have hrow (q : Point) (hq : q ∈ S) := wide_cross_decay_sum S q K L s t₀ A
    hK hL0 hs hs1 ht0 ht2 hA ⟨(hS q hq).1,(hS q hq).2.1⟩ (hangle q hq)
    (fun p hp => ⟨(hS p hp).1,(hS p hp).2.1,(hS p hp).2.2.1⟩)
  have hcard := wide_coarse_card S K L s t₀ A hK hL hs hsK hA hS hangle
  calc
    _ ≤ ∑ q ∈ S, (256*(64/63 : ℝ))*(5832*A)*(1+1/(K*s^2))*(1+1/(L*s)) := sum_le_sum hrow
    _ = S.card*((256*(64/63 : ℝ))*(5832*A)*(1+1/(K*s^2))*(1+1/(L*s))) := by simp
    _ ≤ (162*A*(s*K*L))*((256*(64/63 : ℝ))*(5832*A)*(1+1/(K*s^2))*(1+1/(L*s))) := by gcongr
    _ = _ := by ring

theorem wide_same_pairs_decay_sum (S : Finset Point) (K L s t₀ A : ℝ)
    (hK : 0 < K) (hL : 1 ≤ L) (hs : 0 < s) (hs1 : s ≤ 1) (hsK : 1 ≤ s*K)
    (ht0 : 0 ≤ t₀) (ht2 : t₀ ≤ 2) (hA : 1 ≤ A)
    (hS : ∀ p ∈ S, K ≤ (p.1 : ℝ) ∧ (p.1 : ℝ) < 2*K ∧
      L ≤ (p.2 : ℝ) ∧ (p.2 : ℝ) < 2*L)
    (hangle : ∀ p ∈ S, |Real.sqrt ((p.1 : ℝ)/K)-t₀| ≤ A*s) :
    ∑ q ∈ S, ∑ p ∈ S.filter (fun p => p.1=q.1), ((1+distance K L s t₀ p q)^8)⁻¹ ≤
      (162*(256*(64/63 : ℝ))*27*A)*(s*K*L*(1+1/(K*s^2))) := by
  have hA0 : 0 < A := by linarith
  have hL0 : 0 < L := by linarith
  have hrow (q : Point) (_hq : q ∈ S) := same_ray_decay_sum (S.filter (fun p => p.1=q.1)) q
    K L s t₀ hK hL0 hs hs1 ht0 ht2 (fun p hp => (mem_filter.mp hp).2)
  have hcard := wide_coarse_card S K L s t₀ A hK hL hs hsK hA hS hangle
  calc
    _ ≤ ∑ q ∈ S, (256*(64/63 : ℝ))*27*(1+1/(K*s^2)) := sum_le_sum hrow
    _ = S.card*((256*(64/63 : ℝ))*27*(1+1/(K*s^2))) := by simp
    _ ≤ (162*A*(s*K*L))*((256*(64/63 : ℝ))*27*(1+1/(K*s^2))) := by gcongr
    _ = _ := by ring

theorem relation_decay_sum (S : Finset Point) (F : Finset (Point × Point))
    (hF : F ⊆ S ×ˢ S) (K L s t₀ A : ℝ)
    (hK : 0 < K) (hL : 1 ≤ L) (hs : 0 < s) (hs1 : s ≤ 1) (hsK : 1 ≤ s*K)
    (ht0 : 0 ≤ t₀) (ht2 : t₀ ≤ 2) (hA : 1 ≤ A)
    (hS : ∀ p ∈ S, K ≤ (p.1 : ℝ) ∧ (p.1 : ℝ) < 2*K ∧
      L ≤ (p.2 : ℝ) ∧ (p.2 : ℝ) < 2*L)
    (hangle : ∀ p ∈ S, |Real.sqrt ((p.1 : ℝ)/K)-t₀| ≤ A*s) :
    ∑ p ∈ F, ((1+distance K L s t₀ p.1 p.2)^8)⁻¹ ≤
      (162*(256*(64/63 : ℝ))*5832*A^2)*
        (s*K*L*(1+1/(K*s^2))*(1+1/(L*s))) := by
  apply (sum_le_sum_of_subset_of_nonneg hF (fun p _ _ => by positivity)).trans
  rw [sum_product, sum_comm]
  exact wide_all_pairs_decay_sum S K L s t₀ A hK hL hs hs1 hsK ht0 ht2 hA hS hangle

theorem same_relation_decay_sum (S : Finset Point) (F : Finset (Point × Point))
    (hF : F ⊆ (S ×ˢ S).filter (fun p => p.1.1=p.2.1)) (K L s t₀ A : ℝ)
    (hK : 0 < K) (hL : 1 ≤ L) (hs : 0 < s) (hs1 : s ≤ 1) (hsK : 1 ≤ s*K)
    (ht0 : 0 ≤ t₀) (ht2 : t₀ ≤ 2) (hA : 1 ≤ A)
    (hS : ∀ p ∈ S, K ≤ (p.1 : ℝ) ∧ (p.1 : ℝ) < 2*K ∧
      L ≤ (p.2 : ℝ) ∧ (p.2 : ℝ) < 2*L)
    (hangle : ∀ p ∈ S, |Real.sqrt ((p.1 : ℝ)/K)-t₀| ≤ A*s) :
    ∑ p ∈ F, ((1+distance K L s t₀ p.1 p.2)^8)⁻¹ ≤
      (162*(256*(64/63 : ℝ))*27*A)*(s*K*L*(1+1/(K*s^2))) := by
  apply (sum_le_sum_of_subset_of_nonneg hF (fun p _ _ => by positivity)).trans
  rw [sum_filter, sum_product, sum_comm]
  simp_rw [← sum_filter]
  exact wide_same_pairs_decay_sum S K L s t₀ A hK hL hs hs1 hsK ht0 ht2 hA hS hangle

end
end CircleDivisor.EnergyV3.DensitySums
