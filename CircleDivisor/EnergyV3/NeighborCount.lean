import CircleDivisor.EnergyV3.PairedCountReal
import CircleDivisor.ConeGeometry
import CircleDivisor.EnergyV3.AdaptedMetric

/-! The actual integer-neighbor count of Appendix A.6.  These lemmas concern
the real square-root cone frequencies, rather than abstract separation data. -/
namespace CircleDivisor.EnergyV3.NeighborCount
open Finset
noncomputable section

theorem sqrt_parameter_bounds {K k : ℝ} (hK : 0 < K) (hk : K ≤ k) (hk' : k < 2 * K) :
    1 ≤ Real.sqrt (k / K) ∧ Real.sqrt (k / K) ≤ 2 ∧
      K * (Real.sqrt (k / K)) ^ 2 = k := by
  have hq : 1 ≤ k / K := (le_div_iff₀ hK).mpr (by simpa using hk)
  have hq' : k / K < 2 := (div_lt_iff₀ hK).mpr hk'
  have hs := Real.sq_sqrt (by linarith : 0 ≤ k / K)
  refine ⟨?_, ?_, ?_⟩
  · nlinarith [Real.sqrt_nonneg (k / K)]
  · nlinarith [Real.sqrt_nonneg (k / K)]
  · rw [hs]; field_simp

theorem index_distance_of_parameter_distance {K k k' T : ℝ} (hK : 0 < K)
    (hk : K ≤ k) (hk' : k < 2 * K) (hj : K ≤ k') (hj' : k' < 2 * K)
    (ht : |Real.sqrt (k / K) - Real.sqrt (k' / K)| ≤ T) :
    |k - k'| ≤ 4 * K * T := by
  rcases sqrt_parameter_bounds hK hk hk' with ⟨h1,h2,h3⟩
  rcases sqrt_parameter_bounds hK hj hj' with ⟨j1,j2,j3⟩
  have hsum : |Real.sqrt (k / K) + Real.sqrt (k' / K)| ≤ 4 := by
    rw [abs_of_nonneg (by positivity)]; linarith
  calc
    _ = K * (|Real.sqrt (k / K) - Real.sqrt (k' / K)| *
        |Real.sqrt (k / K) + Real.sqrt (k' / K)|) := by
      have he : k - k' = K * ((Real.sqrt (k / K) - Real.sqrt (k' / K)) *
          (Real.sqrt (k / K) + Real.sqrt (k' / K))) := by nlinarith
      rw [he, abs_mul, abs_mul, abs_of_pos hK]
    _ ≤ K * (T * 4) := mul_le_mul_of_nonneg_left
      (mul_le_mul ht hsum (abs_nonneg _) ((abs_nonneg _).trans ht)) hK.le
    _ = _ := by ring

/-- Bounds on the first two *actual adapted coordinates* force bounds on the
two integer indices. The arbitrary center `t₀` is retained. -/
theorem actual_frequency_neighbor_separation
    {K L s N t₀ k k' l l' : ℝ}
    (hK : 0 < K) (hL : 0 < L) (hs : 0 < s)
    (hk : K ≤ k) (hk' : k < 2 * K) (hj : K ≤ k') (hj' : k' < 2 * K)
    (hl : L ≤ l)
    (hangle : |Real.sqrt (k' / K) - t₀| ≤ s)
    (hzero : |ConeGeometry.adapted t₀
        (ConeGeometry.frequency K L k l - ConeGeometry.frequency K L k' l') 0| ≤
      N / (K * L * s ^ 2))
    (hone : |ConeGeometry.adapted t₀
        (ConeGeometry.frequency K L k l - ConeGeometry.frequency K L k' l') 1| ≤
      N / (K * L * s)) :
    |l - l'| ≤ N / (K * s ^ 2) ∧ |k - k'| ≤ 8 * N / (L * s) := by
  have hr : 1 ≤ l / L := (le_div_iff₀ hL).mpr (by simpa using hl)
  have hz : |l / L - l' / L| ≤ N / (K * L * s ^ 2) := by
    simpa [ConeGeometry.adapted, ConeGeometry.frequency] using hzero
  have ho : |(l / L) * (Real.sqrt (k / K) - t₀) -
      (l' / L) * (Real.sqrt (k' / K) - t₀)| ≤ N / (K * L * s) := by
    convert hone using 1
    congr 1
    simp [ConeGeometry.adapted, ConeGeometry.frequency]
    ring
  have hsep := ConeGeometry.parameter_separation hr hs.le hangle hz ho
  have hsimp : N / (K * L * s) + N / (K * L * s ^ 2) * s =
      2 * N / (K * L * s) := by field_simp; ring
  rw [hsimp] at hsep
  constructor
  · rw [← sub_div, abs_div, abs_of_pos hL] at hz
    have hh := (div_le_iff₀ hL).mp hz
    calc
      _ ≤ N / (K * L * s ^ 2) * L := hh
      _ = _ := by field_simp
  · have hh := index_distance_of_parameter_distance hK hk hk' hj hj' hsep
    calc
      _ ≤ 4 * K * (2 * N / (K * L * s)) := hh
      _ = _ := by field_simp; ring

def integerNeighborhood (center : ℤ) (A : ℝ) : Finset ℤ :=
  Icc (center - (Nat.ceil A : ℤ)) (center + Nat.ceil A)

theorem mem_integerNeighborhood {center k : ℤ} {A : ℝ}
    (h : |((k - center : ℤ) : ℝ)| ≤ A) : k ∈ integerNeighborhood center A := by
  have hb : |k - center| ≤ (Nat.ceil A : ℤ) := by exact_mod_cast h.trans (Nat.le_ceil A)
  have hbounds := abs_le.mp hb
  simp only [integerNeighborhood, mem_Icc]
  omega

theorem card_integerNeighborhood (center : ℤ) (A : ℝ) :
    (integerNeighborhood center A).card = 2 * Nat.ceil A + 1 := by
  simp [integerNeighborhood]
  omega

theorem card_integerNeighborhood_le (center : ℤ) {A : ℝ} (hA : 0 ≤ A) :
    ((integerNeighborhood center A).card : ℝ) ≤ 3 * (1 + A) := by
  rw [card_integerNeighborhood]
  push_cast
  have := Nat.ceil_lt_add_one hA
  linarith

/-- Cardinality of every actual subset of the integer rectangle. -/
theorem integer_neighbor_count (S : Finset (ℤ × ℤ)) (center : ℤ × ℤ)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hS : ∀ p ∈ S, |((p.2 - center.2 : ℤ) : ℝ)| ≤ A ∧
      |((p.1 - center.1 : ℤ) : ℝ)| ≤ B) :
    (S.card : ℝ) ≤ 9 * (1 + A) * (1 + B) := by
  have hsub : S ⊆ integerNeighborhood center.1 B ×ˢ integerNeighborhood center.2 A := by
    intro p hp
    exact mem_product.mpr ⟨mem_integerNeighborhood (hS p hp).2, mem_integerNeighborhood (hS p hp).1⟩
  have hc : (S.card : ℝ) ≤ ((integerNeighborhood center.1 B).card : ℝ) *
      ((integerNeighborhood center.2 A).card : ℝ) := by
    have hh := card_le_card hsub
    rw [card_product] at hh
    exact_mod_cast hh
  calc
    _ ≤ _ := hc
    _ ≤ (3 * (1 + B)) * (3 * (1 + A)) :=
      mul_le_mul (card_integerNeighborhood_le _ hB) (card_integerNeighborhood_le _ hA)
        (by positivity) (by positivity)
    _ = _ := by ring

theorem same_ray_neighbor_count (S : Finset (ℤ × ℤ)) (center : ℤ × ℤ)
    {A : ℝ} (hA : 0 ≤ A)
    (hS : ∀ p ∈ S, p.1 = center.1 ∧ |((p.2 - center.2 : ℤ) : ℝ)| ≤ A) :
    (S.card : ℝ) ≤ 3 * (1 + A) := by
  have hm : Set.MapsTo Prod.snd (S : Set (ℤ × ℤ)) (integerNeighborhood center.2 A : Set ℤ) :=
    fun p hp => mem_integerNeighborhood (hS p hp).2
  have hi : Set.InjOn Prod.snd (S : Set (ℤ × ℤ)) := by
    intro p hp q hq heq
    exact Prod.ext ((hS p hp).1.trans (hS q hq).1.symm) heq
  have hc : (S.card : ℝ) ≤ ((integerNeighborhood center.2 A).card : ℝ) := by
    exact_mod_cast card_le_card_of_injOn Prod.snd hm hi
  exact hc.trans (card_integerNeighborhood_le _ hA)

/-- A complete frequency-metric-to-cardinality statement, including the
irrational frequency coordinate and the two integer widths. -/
theorem actual_dual_neighbor_count (S : Finset (ℤ × ℤ)) (center : ℤ × ℤ)
    (K L s N t₀ : ℝ) (hK : 0 < K) (hL : 0 < L) (hs : 0 < s) (hs1 : s ≤ 1)
    (ht0 : 0 ≤ t₀) (ht2 : t₀ ≤ 2) (hN : 0 ≤ N)
    (hcenter : K ≤ (center.1 : ℝ) ∧ (center.1 : ℝ) < 2*K)
    (hangle : |Real.sqrt ((center.1 : ℝ) / K) - t₀| ≤ s)
    (hS : ∀ p ∈ S, K ≤ (p.1 : ℝ) ∧ (p.1 : ℝ) < 2*K ∧ L ≤ (p.2 : ℝ))
    (hmetric : ∀ p ∈ S, ‖AdaptedMetric.dualCoordinates (K*L) s t₀
        (ConeGeometry.frequency K L p.1 p.2 - ConeGeometry.frequency K L center.1 center.2)‖ ≤ N) :
    (S.card : ℝ) ≤ 5832 * (1 + N/(K*s^2)) * (1 + N/(L*s)) := by
  have ha : 0 ≤ N/(K*s^2) := by positivity
  have hb : 0 ≤ N/(L*s) := by positivity
  have hsep p (hp : p ∈ S) :
      |((p.2-center.2 : ℤ) : ℝ)| ≤ (9*N)/(K*s^2) ∧
      |((p.1-center.1 : ℤ) : ℝ)| ≤ (72*N)/(L*s) := by
    have hm := AdaptedMetric.transpose_controls_adapted (mul_pos hK hL) hs hs1 ht0 ht2
      (ConeGeometry.frequency K L p.1 p.2 - ConeGeometry.frequency K L center.1 center.2)
    have hz : |ConeGeometry.adapted t₀
        (ConeGeometry.frequency K L p.1 p.2 - ConeGeometry.frequency K L center.1 center.2) 0| ≤
        (9*N)/(K*L*s^2) := by
      apply (le_div_iff₀ (by positivity : 0 < K*L*s^2)).mpr
      nlinarith [hm.1, hmetric p hp]
    have ho : |ConeGeometry.adapted t₀
        (ConeGeometry.frequency K L p.1 p.2 - ConeGeometry.frequency K L center.1 center.2) 1| ≤
        (9*N)/(K*L*s) := by
      apply (le_div_iff₀ (by positivity : 0 < K*L*s)).mpr
      nlinarith [hm.2.1, hmetric p hp]
    have hh := actual_frequency_neighbor_separation hK hL hs
      (hS p hp).1 (hS p hp).2.1 hcenter.1 hcenter.2 (hS p hp).2.2 hangle hz ho
    simpa only [Int.cast_sub, show (8:ℝ)*(9*N) = 72*N by ring] using hh
  have hc := integer_neighbor_count S center (by positivity : 0 ≤ (9*N)/(K*s^2))
    (by positivity : 0 ≤ (72*N)/(L*s)) hsep
  have he1 : (9*N)/(K*s^2) = 9*(N/(K*s^2)) := by ring
  have he2 : (72*N)/(L*s) = 72*(N/(L*s)) := by ring
  rw [he1, he2] at hc
  calc
    _ ≤ _ := hc
    _ ≤ 9 * (9 * (1 + N/(K*s^2))) * (72 * (1 + N/(L*s))) := by gcongr <;> linarith
    _ = _ := by ring

/-- The shell summation really is uniformly finite, with an explicit constant. -/
theorem shell_series_bound {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Summable (fun j : ℕ => (1 / 256 : ℝ) ^ j * (1 + 2 ^ j * a) * (1 + 2 ^ j * b)) ∧
    (∑' j : ℕ, (1 / 256 : ℝ) ^ j * (1 + 2 ^ j * a) * (1 + 2 ^ j * b)) ≤
      (64 / 63 : ℝ) * (1 + a) * (1 + b) := by
  have hgeo : Summable (fun j : ℕ => (1 / 64 : ℝ) ^ j) := summable_geometric_of_norm_lt_one (by norm_num)
  have hmajor := (hgeo.mul_right (1 + a)).mul_right (1 + b)
  have hnonneg (j : ℕ) : 0 ≤ (1 / 256 : ℝ) ^ j * (1 + 2 ^ j * a) * (1 + 2 ^ j * b) := by positivity
  have hbound (j : ℕ) : (1 / 256 : ℝ) ^ j * (1 + 2 ^ j * a) * (1 + 2 ^ j * b) ≤
      (1 / 64 : ℝ) ^ j * (1 + a) * (1 + b) := by
    have htwo : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    have hfa : 1 + 2 ^ j * a ≤ 2 ^ j * (1 + a) := by nlinarith
    have hfb : 1 + 2 ^ j * b ≤ 2 ^ j * (1 + b) := by nlinarith
    calc
      _ ≤ (1 / 256 : ℝ) ^ j * (2 ^ j * (1 + a)) * (2 ^ j * (1 + b)) := by gcongr
      _ = (1 / 64 : ℝ) ^ j * (1 + a) * (1 + b) := by
        have he : (1 / 256 : ℝ) ^ j * (2 : ℝ) ^ j * 2 ^ j = (1 / 64 : ℝ) ^ j := by
          rw [← mul_pow, ← mul_pow]
          norm_num
        calc
          _ = ((1 / 256 : ℝ) ^ j * 2 ^ j * 2 ^ j) * (1 + a) * (1 + b) := by ring
          _ = _ := by rw [he]
  have hs := Summable.of_nonneg_of_le hnonneg hbound hmajor
  refine ⟨hs, (hs.tsum_le_tsum hbound hmajor).trans_eq ?_⟩
  rw [tsum_mul_right, tsum_mul_right, tsum_geometric_of_norm_lt_one (by norm_num : ‖(1 / 64 : ℝ)‖ < 1)]
  norm_num

end
end CircleDivisor.EnergyV3.NeighborCount
