import CircleDivisor.EnergyV3.CoarseDecomposition
import CircleDivisor.EnergyV3.RefinedEnergy

/-! The pair relations of the canonical projections satisfy the precise
two-width counting hypotheses. All angular and integer widths are derived. -/
namespace CircleDivisor.EnergyV3.CoarseWindows
noncomputable section
open GuthMaldague CoarseDecomposition Finset
abbrev Space := GuthMaldague.Space

def frequency (K L ρ : ℝ) (p : Point) : Space :=
  AngularAtoms.rotate ρ (LinearTransport.circularFrequency
    (FourierLocalization.coneFrequency K L p.1 p.2))

def widthConstant : ℝ := 32*Real.pi

theorem widthConstant_one_le : 1≤widthConstant := by
  unfold widthConstant
  linarith [Real.pi_gt_three]

theorem cap_integer_diameter (K L ρ : ℝ) (hK : 0<K) (hL : 0<L)
    (hρ : 0≤ρ) (hρu : ρ≤1) (n : ℕ) (i : CapIndex n) (p q : Point)
    (hp : K≤(p.1:ℝ) ∧ (p.1:ℝ)<2*K ∧ L≤(p.2:ℝ))
    (hq : K≤(q.1:ℝ) ∧ (q.1:ℝ)<2*K ∧ L≤(q.2:ℝ))
    (hpc : frequency K L ρ p∈cap n i) (hqc : frequency K L ρ q∈cap n i) :
    |((p.1-q.1:ℤ):ℝ)| ≤ widthConstant*scale n*K := by
  unfold frequency at hpc hqc
  rw [AngularAtoms.circularFrequency_generator K L hK hL _ _ hp.1] at hpc
  rw [AngularAtoms.circularFrequency_generator K L hK hL _ _ hq.1] at hqc
  have hh := AngularAtoms.same_cap_index_diameter n i ρ K (p.1:ℝ) (q.1:ℝ)
    ((p.2:ℝ)/L) ((q.2:ℝ)/L) hρ hρu hK hp.1 hp.2.1 hq.1 hq.2.1
    (div_pos (lt_of_lt_of_le hL hp.2.2) hL) (div_pos (lt_of_lt_of_le hL hq.2.2) hL) hpc hqc
  simpa only [Int.cast_sub, widthConstant, AngularAtoms.angularWidth,
    show 16*K*(2*Real.pi*scale n)=32*Real.pi*scale n*K by ring] using hh

theorem finest_width (K L : ℝ) (hK : 0<K) (hL : 0<L) (n : ℕ) (hR : K*L≤radius n) :
    scale n*K ≤ Real.sqrt (K/L) := by
  have hsq : scale n^2*radius n=1 := by
    unfold scale radius
    rw [inv_pow, ← pow_mul, Nat.mul_comm n 2, pow_mul]
    norm_num
  have hnn := scale_pos n
  have hbound : (scale n*K)^2 ≤ K/L := by
    apply (le_div_iff₀ hL).mpr
    have hh := mul_le_mul_of_nonneg_left hR (sq_nonneg (scale n))
    rw [hsq] at hh
    nlinarith [mul_nonneg hK.le (sub_nonneg.mpr hh)]
  exact (Real.le_sqrt (by positivity) (by positivity)).mpr hbound

theorem coarsePoints_cap (n j : ℕ) (I : Finset Point) (θ : ℤ→CapIndex n)
    (K L ρ : ℝ) (hcap : ∀ p∈I, frequency K L ρ p∈cap n (θ p.1))
    (i : CapIndex j) (p : Point) (hp : p∈coarsePoints n j I θ i) :
    frequency K L ρ p∈cap j i := by
  obtain ⟨hp,hchild⟩ := mem_filter.mp hp
  have hsub : cap n (θ p.1) ⊆ cap j i := by simpa [fineChildren] using hchild
  exact hsub (hcap p hp)

theorem sameWindow (n j : ℕ) (I : Finset Point) (θ : ℤ→CapIndex n)
    (K L ρ : ℝ) (hK : 0<K) (hL : 0<L) (hρ : 0≤ρ) (hρu : ρ≤1)
    (hI : ∀ p∈I, K≤(p.1:ℝ) ∧ (p.1:ℝ)<2*K ∧ L≤(p.2:ℝ) ∧ (p.2:ℝ)<2*L)
    (hcap : ∀ p∈I, frequency K L ρ p∈cap n (θ p.1)) (i : CapIndex j) :
    PairEnergies.SameWindow K L (widthConstant*scale j*K) (samePairs (coarsePoints n j I θ i)) := by
  let S := coarsePoints n j I θ i
  have hs (p : Point) (hp : p∈S) := hI p (coarsePoints_subset n j I θ i hp)
  have hc (p : Point) (hp : p∈S) := coarsePoints_cap n j I θ K L ρ hcap i p hp
  constructor
  · intro p hp
    obtain ⟨hp,hq⟩ := mem_product.mp (mem_filter.mp hp).1
    exact ⟨⟨(hs p.1 hp).1,(hs p.1 hp).2.1⟩,⟨(hs p.2 hq).1,(hs p.2 hq).2.1⟩,
      (hs p.1 hp).2.2,(hs p.2 hq).2.2⟩
  · intro p hp
    exact (mem_filter.mp hp).2
  · intro p hp r hr
    have hp := (mem_product.mp (mem_filter.mp hp).1).1
    have hr := (mem_product.mp (mem_filter.mp hr).1).1
    exact cap_integer_diameter K L ρ hK hL hρ hρu j i p.1 r.1
      ⟨(hs p.1 hp).1,(hs p.1 hp).2.1,(hs p.1 hp).2.2.1⟩
      ⟨(hs r.1 hr).1,(hs r.1 hr).2.1,(hs r.1 hr).2.2.1⟩ (hc p.1 hp) (hc r.1 hr)

theorem crossWindow (n j : ℕ) (I : Finset Point) (θ : ℤ→CapIndex n)
    (K L ρ : ℝ) (hK : 0<K) (hL : 0<L) (hρ : 0≤ρ) (hρu : ρ≤1) (hR : K*L≤radius n)
    (hI : ∀ p∈I, K≤(p.1:ℝ) ∧ (p.1:ℝ)<2*K ∧ L≤(p.2:ℝ) ∧ (p.2:ℝ)<2*L)
    (hcap : ∀ p∈I, frequency K L ρ p∈cap n (θ p.1)) (i : CapIndex j) :
    PairEnergies.CrossWindow K L (widthConstant*Real.sqrt (K/L)) (widthConstant*scale j*K)
      (crossPairs n (coarsePoints n j I θ i) θ) := by
  let S := coarsePoints n j I θ i
  have hs (p : Point) (hp : p∈S) := hI p (coarsePoints_subset n j I θ i hp)
  have hc (p : Point) (hp : p∈S) := coarsePoints_cap n j I θ K L ρ hcap i p hp
  constructor
  · intro p hp
    obtain ⟨hp,hq⟩ := mem_product.mp (mem_filter.mp (mem_filter.mp hp).1).1
    exact ⟨⟨(hs p.1 hp).1,(hs p.1 hp).2.1⟩,⟨(hs p.2 hq).1,(hs p.2 hq).2.1⟩,
      (hs p.1 hp).2.2,(hs p.2 hq).2.2⟩
  · intro p hp
    exact (mem_filter.mp hp).2
  · intro p hp
    obtain ⟨⟨hpp,hθ⟩,hne⟩ := mem_filter.mp hp |>.imp_left mem_filter.mp
    obtain ⟨hp,hq⟩ := mem_product.mp hpp
    have hh := cap_integer_diameter K L ρ hK hL hρ hρu n (θ p.1.1) p.1 p.2
      ⟨(hs p.1 hp).1,(hs p.1 hp).2.1,(hs p.1 hp).2.2.1⟩
      ⟨(hs p.2 hq).1,(hs p.2 hq).2.1,(hs p.2 hq).2.2.1⟩
      (hcap _ (coarsePoints_subset n j I θ i hp))
      (by rw [hθ]; exact hcap _ (coarsePoints_subset n j I θ i hq))
    apply hh.trans
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (finest_width K L hK hL n hR) (by unfold widthConstant; positivity)
  · intro p hp r hr
    have hp := (mem_product.mp (mem_filter.mp (mem_filter.mp hp).1).1).2
    have hr := (mem_product.mp (mem_filter.mp (mem_filter.mp hr).1).1).1
    exact cap_integer_diameter K L ρ hK hL hρ hρu j i p.2 r.1
      ⟨(hs p.2 hp).1,(hs p.2 hp).2.1,(hs p.2 hp).2.2.1⟩
      ⟨(hs r.1 hr).1,(hs r.1 hr).2.1,(hs r.1 hr).2.2.1⟩ (hc p.2 hp) (hc r.1 hr)

end
end CircleDivisor.EnergyV3.CoarseWindows
