import CircleDivisor.EnergyV3.PairedCountReal

namespace CircleDivisor.EnergyV3.SameRayCount
open Finset CircleDivisor.SpacingCount
noncomputable section
abbrev Quadruple := PairedCount.Quadruple

structure Admissible (K L V : ℕ) (x : Quadruple) : Prop where
  base_mem : x.k4 ∈ baseSet K
  l1_mem : x.l1 ∈ radialSet L
  l2_mem : x.l2 ∈ radialSet L
  l3_mem : x.l3 ∈ radialSet L
  first : PairedCount.firstEquation x
  second : PairedCount.secondEquation x
  same1 : x.k1 = x.k2
  same2 : x.k3 = x.k4
  width : x.k1 - x.k4 ∈ differenceSet V

theorem different_rays_force_diagonal {K L V : ℕ} {x : Quadruple}
    (h : Admissible K L V x) (hne : x.k1 ≠ x.k4) : x.l1 = x.l2 ∧ x.l3 = x.l4 := by
  have he := h.second
  have hf := h.first
  dsimp [PairedCount.firstEquation] at hf
  dsimp [PairedCount.secondEquation] at he
  rw [← h.same1, h.same2] at he
  have hm : (x.k1 - x.k4) * (x.l1 - x.l2) = 0 := by nlinarith [congrArg (fun z : ℤ => x.k4 * z) hf]
  have hz := (mul_eq_zero.mp hm).resolve_left (sub_ne_zero.mpr hne)
  omega

def radialCode (x : Quadruple) : ℤ × ℤ × ℤ × ℤ := (x.k4, x.l1, x.l2, x.l3)
def diagonalCode (x : Quadruple) : ℤ × ℤ × ℤ × ℤ := (x.k4, x.k1 - x.k4, x.l1, x.l3)

theorem count_radial (K L V : ℕ) (S : Finset Quadruple)
    (hS : ∀ x ∈ S, Admissible K L V x) (hr : ∀ x ∈ S, x.k1 = x.k4) :
    S.card ≤ K * L ^ 3 := by
  have hi : Set.InjOn radialCode (S : Set Quadruple) := by
    intro x hx y hy heq
    have hxe := (hS x hx).first
    have hye := (hS y hy).first
    have hx1 := (hS x hx).same1
    have hx2 := (hS x hx).same2
    have hy1 := (hS y hy).same1
    have hy2 := (hS y hy).same2
    have hxr := hr x hx
    have hyr := hr y hy
    simp only [radialCode, Prod.mk.injEq] at heq
    dsimp [PairedCount.firstEquation] at hxe hye
    have hl4 : x.l4 = y.l4 := by omega
    cases x; cases y
    simp_all
  have hm : Set.MapsTo radialCode (S : Set Quadruple)
      (↑(baseSet K ×ˢ radialSet L ×ˢ radialSet L ×ˢ radialSet L) : Set (ℤ × ℤ × ℤ × ℤ)) := by
    intro x hx
    exact mem_product.mpr ⟨(hS x hx).base_mem, mem_product.mpr ⟨(hS x hx).l1_mem,
      mem_product.mpr ⟨(hS x hx).l2_mem, (hS x hx).l3_mem⟩⟩⟩
  have hk : (baseSet K).card = K := by simp [baseSet]; omega
  have hl : (radialSet L).card = L := by simp [radialSet]; omega
  simpa [hk, hl, card_product, pow_succ, mul_assoc] using
    card_le_card_of_injOn radialCode hm hi

theorem count_diagonal (K L V : ℕ) (S : Finset Quadruple)
    (hS : ∀ x ∈ S, Admissible K L V x) (hd : ∀ x ∈ S, x.l1 = x.l2 ∧ x.l3 = x.l4) :
    S.card ≤ K * (2 * V + 1) * L ^ 2 := by
  have hi : Set.InjOn diagonalCode (S : Set Quadruple) := by
    intro x hx y hy heq
    have hx1 := (hS x hx).same1
    have hx2 := (hS x hx).same2
    have hy1 := (hS y hy).same1
    have hy2 := (hS y hy).same2
    have hxd := hd x hx
    have hyd := hd y hy
    simp only [diagonalCode, Prod.mk.injEq] at heq
    have hk : x.k1 = y.k1 := by omega
    cases x; cases y
    simp_all
  have hm : Set.MapsTo diagonalCode (S : Set Quadruple)
      (↑(baseSet K ×ˢ differenceSet V ×ˢ radialSet L ×ˢ radialSet L) : Set (ℤ × ℤ × ℤ × ℤ)) := by
    intro x hx
    exact mem_product.mpr ⟨(hS x hx).base_mem, mem_product.mpr ⟨(hS x hx).width,
      mem_product.mpr ⟨(hS x hx).l1_mem, (hS x hx).l3_mem⟩⟩⟩
  have hv : (differenceSet V).card = 2 * V + 1 := by simp [differenceSet]; omega
  have hk : (baseSet K).card = K := by simp [baseSet]; omega
  have hl : (radialSet L).card = L := by simp [radialSet]; omega
  simpa [hk, hl, card_product, hv, pow_two, mul_assoc] using
    card_le_card_of_injOn diagonalCode hm hi

theorem count_quadruples (K L V : ℕ) (hV : 1 ≤ V) (S : Finset Quadruple)
    (hS : ∀ x ∈ S, Admissible K L V x) :
    S.card ≤ K * L ^ 3 + 3 * K * V * L ^ 2 := by
  let R := S.filter (fun x => x.k1 = x.k4)
  let D := S.filter (fun x => x.k1 ≠ x.k4)
  have hc : S.card = R.card + D.card := by
    simpa [R, D] using (card_filter_add_card_filter_not (s := S) (p := fun x => x.k1 = x.k4)).symm
  have hr := count_radial K L V R (fun x hx => hS x (mem_filter.mp hx).1)
    (fun x hx => (mem_filter.mp hx).2)
  have hd := count_diagonal K L V D (fun x hx => hS x (mem_filter.mp hx).1)
    (fun x hx => different_rays_force_diagonal (hS x (mem_filter.mp hx).1) (mem_filter.mp hx).2)
  rw [hc]
  calc
    _ ≤ K * L ^ 3 + K * (2 * V + 1) * L ^ 2 := add_le_add hr hd
    _ ≤ K * L ^ 3 + K * (3 * V) * L ^ 2 := by gcongr; omega
    _ = _ := by ring

structure RealAdmissible (K L V : ℝ) (x : Quadruple) : Prop where
  base_mem : (x.k4 : ℝ) ∈ Set.Ico K (2 * K)
  l1_mem : (x.l1 : ℝ) ∈ Set.Ico L (2 * L)
  l2_mem : (x.l2 : ℝ) ∈ Set.Ico L (2 * L)
  l3_mem : (x.l3 : ℝ) ∈ Set.Ico L (2 * L)
  first : PairedCount.firstEquation x
  second : PairedCount.secondEquation x
  same1 : x.k1 = x.k2
  same2 : x.k3 = x.k4
  width : |((x.k1 - x.k4 : ℤ) : ℝ)| ≤ V

theorem RealAdmissible.ceiling {K L V : ℝ} {x : Quadruple}
    (h : RealAdmissible K L V x) (hK : 1 ≤ K) (hL : 1 ≤ L) :
    Admissible (Nat.ceil K) (Nat.ceil L) (Nat.ceil V) x := by
  refine ⟨PairedCount.real_interval_to_ceiling K hK x.k4 h.base_mem,
    PairedCount.real_interval_to_ceiling L hL x.l1 h.l1_mem,
    PairedCount.real_interval_to_ceiling L hL x.l2 h.l2_mem,
    PairedCount.real_interval_to_ceiling L hL x.l3 h.l3_mem,
    h.first, h.second, h.same1, h.same2, ?_⟩
  simp only [differenceSet, mem_Icc]
  apply abs_le.mp
  exact_mod_cast h.width.trans (Nat.le_ceil V)

theorem count_real (K L V : ℝ) (hK : 1 ≤ K) (hL : 1 ≤ L) (hV : 1 ≤ V)
    (S : Finset Quadruple) (hS : ∀ x ∈ S, RealAdmissible K L V x) :
    (S.card : ℝ) ≤ 48 * (K * V * L ^ 2 + K * L ^ 3) := by
  have hc : (S.card : ℝ) ≤ (Nat.ceil K : ℝ) * (Nat.ceil L : ℝ) ^ 3 +
      3 * (Nat.ceil K : ℝ) * (Nat.ceil V : ℝ) * (Nat.ceil L : ℝ) ^ 2 := by
    exact_mod_cast count_quadruples (Nat.ceil K) (Nat.ceil L) (Nat.ceil V)
      (Nat.one_le_ceil_iff.mpr (by linarith)) S (fun x hx => (hS x hx).ceiling hK hL)
  have hk := PairedCount.ceil_le_twice K hK
  have hl := PairedCount.ceil_le_twice L hL
  have hv := PairedCount.ceil_le_twice V hV
  calc
    _ ≤ _ := hc
    _ ≤ (2 * K) * (2 * L) ^ 3 + 3 * (2 * K) * (2 * V) * (2 * L) ^ 2 := by gcongr
    _ ≤ _ := by nlinarith [show 0 ≤ K * L ^ 3 by positivity]

end
end CircleDivisor.EnergyV3.SameRayCount
