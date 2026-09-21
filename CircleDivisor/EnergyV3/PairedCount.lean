import CircleDivisor.SpacingCount

/-! The two independent widths in §2 of the September 2026 energy manuscript.
All cardinalities are those of actual finite sets of integer solutions. -/
namespace CircleDivisor.EnergyV3.PairedCount
open Finset
open CircleDivisor.SpacingCount (baseSet radialSet differenceSet divisorsIn DivisorBound)
noncomputable section

structure Coordinates where
  base : ℤ
  d1 : ℤ
  d2 : ℤ
  u : ℤ
  a : ℤ
  l1 : ℤ
  l3 : ℤ
  deriving DecidableEq

def numerator (x : Coordinates) : ℤ := x.d1 * x.l1 + x.d2 * x.l3
def equation (x : Coordinates) : Prop := x.u * x.a = -numerator x

structure Bounded (K L W V : ℕ) (x : Coordinates) : Prop where
  base_mem : x.base ∈ baseSet K
  d1_mem : x.d1 ∈ differenceSet W
  d2_mem : x.d2 ∈ differenceSet W
  u_mem : x.u ∈ differenceSet V
  a_mem : x.a ∈ differenceSet L
  l1_mem : x.l1 ∈ radialSet L
  l3_mem : x.l3 ∈ radialSet L
  d1_ne : x.d1 ≠ 0
  d2_ne : x.d2 ≠ 0
  eqn : equation x

theorem Bounded.l1_pos {K L W V : ℕ} {x : Coordinates}
    (h : Bounded K L W V x) (hL : 1 ≤ L) : 0 < x.l1 := by
  have := h.l1_mem
  simp only [radialSet, mem_Ico] at this
  omega

theorem Bounded.l3_pos {K L W V : ℕ} {x : Coordinates}
    (h : Bounded K L W V x) (hL : 1 ≤ L) : 0 < x.l3 := by
  have := h.l3_mem
  simp only [radialSet, mem_Ico] at this
  omega

theorem Bounded.abs_product {K L W V : ℕ} {x : Coordinates}
    (h : Bounded K L W V x) : |x.d1 * x.l1| ≤ 2 * (L : ℤ) * W := by
  have hd : |x.d1| ≤ (W : ℤ) := abs_le.mpr (by simpa [differenceSet] using h.d1_mem)
  have hl : |x.l1| ≤ 2 * (L : ℤ) := by
    have := h.l1_mem
    simp only [radialSet, mem_Ico] at this
    exact abs_le.mpr ⟨by omega, by omega⟩
  rw [abs_mul]
  calc
    _ ≤ (W : ℤ) * (2 * L) := mul_le_mul hd hl (abs_nonneg _) (by positivity)
    _ = _ := by ring

theorem Bounded.abs_numerator {K L W V : ℕ} {x : Coordinates}
    (h : Bounded K L W V x) : |numerator x| ≤ 2 * (L : ℤ) * (2 * W) := by
  have hd : |x.d2| ≤ (W : ℤ) := abs_le.mpr (by simpa [differenceSet] using h.d2_mem)
  have hl : |x.l3| ≤ 2 * (L : ℤ) := by
    have := h.l3_mem
    simp only [radialSet, mem_Ico] at this
    exact abs_le.mpr ⟨by omega, by omega⟩
  have hp := mul_le_mul hd hl (abs_nonneg _) (by positivity : (0 : ℤ) ≤ W)
  have hp1 := h.abs_product
  have ht := abs_add_le (x.d1 * x.l1) (x.d2 * x.l3)
  rw [abs_mul] at hp1
  simp only [numerator, abs_mul] at ht ⊢
  nlinarith

theorem card_le_fibers {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (T : Finset β) (f : α → β) (D : ℕ)
    (hf : ∀ x ∈ S, f x ∈ T)
    (hD : ∀ y ∈ T, (S.filter (fun x => f x = y)).card ≤ D) :
    S.card ≤ T.card * D := by
  calc
    _ = ∑ y ∈ T, (S.filter (fun x => f x = y)).card :=
      Finset.card_eq_sum_card_fiberwise hf
    _ ≤ ∑ _y ∈ T, D := Finset.sum_le_sum hD
    _ = _ := by simp

def nonzeroCode (x : Coordinates) : ℤ × ℤ × ℤ × ℤ × ℤ :=
  (x.base, x.d1, x.d2, x.l1, x.l3)

theorem nonzeroCode_inj {x y : Coordinates} (hx : equation x) (hy : equation y)
    (hn : numerator x ≠ 0) (hc : nonzeroCode x = nonzeroCode y) (ha : x.a = y.a) :
    x = y := by
  simp only [nonzeroCode, Prod.mk.injEq] at hc
  have hnum : numerator x = numerator y := by simp [numerator, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2]
  have ha0 : x.a ≠ 0 := by intro hz; simp [equation, hz] at hx; exact hn (by omega)
  have hu : x.u = y.u := mul_right_cancel₀ ha0 (by
    dsimp [equation] at hx hy
    rw [← ha, ← hnum] at hy
    exact hx.trans hy.symm)
  cases x; cases y
  simp_all

theorem count_nonzero (K L W V D : ℕ) (S : Finset Coordinates)
    (hS : ∀ x ∈ S, Bounded K L W V x) (hn : ∀ x ∈ S, numerator x ≠ 0)
    (hD : DivisorBound L (2 * W) D) :
    S.card ≤ (baseSet K).card * (differenceSet W).card ^ 2 * (radialSet L).card ^ 2 * D := by
  let T := baseSet K ×ˢ differenceSet W ×ˢ differenceSet W ×ˢ radialSet L ×ˢ radialSet L
  have hb : S.card ≤ T.card * D := by
    apply card_le_fibers S T nonzeroCode D
    · intro x hx
      exact mem_product.mpr ⟨(hS x hx).base_mem, mem_product.mpr ⟨(hS x hx).d1_mem,
        mem_product.mpr ⟨(hS x hx).d2_mem, mem_product.mpr ⟨(hS x hx).l1_mem, (hS x hx).l3_mem⟩⟩⟩⟩
    · intro y hy
      let F := S.filter (fun x => nonzeroCode x = y)
      by_cases hF : F.Nonempty
      · obtain ⟨x₀, hx₀⟩ := hF
        have hx₀S := (mem_filter.mp hx₀).1
        have hmap : Set.MapsTo Coordinates.a (F : Set Coordinates)
            (divisorsIn L (numerator x₀) : Set ℤ) := by
          intro x hx
          have hxS := (mem_filter.mp hx).1
          have hc := (mem_filter.mp hx).2.trans (mem_filter.mp hx₀).2.symm
          simp only [nonzeroCode, Prod.mk.injEq] at hc
          have hnum : numerator x = numerator x₀ := by
            simp [numerator, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2]
          have ha := (hS x hxS).a_mem
          simp only [differenceSet, mem_Icc] at ha
          change x.a ∈ divisorsIn L (numerator x₀)
          refine mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩, ⟨-x.u, ?_⟩⟩
          have he := (hS x hxS).eqn
          dsimp [equation] at he
          rw [← hnum]
          nlinarith
        have hinj : Set.InjOn Coordinates.a (F : Set Coordinates) := by
          intro x hx z hz ha
          exact nonzeroCode_inj (hS x (mem_filter.mp hx).1).eqn
            (hS z (mem_filter.mp hz).1).eqn (hn x (mem_filter.mp hx).1)
            ((mem_filter.mp hx).2.trans (mem_filter.mp hz).2.symm) ha
        exact (card_le_card_of_injOn Coordinates.a hmap hinj).trans
          (hD (numerator x₀) (hn x₀ hx₀S) (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using (hS x₀ hx₀S).abs_numerator))
      · change F.card ≤ D
        simp [not_nonempty_iff_eq_empty.mp hF]
  simpa [T, card_product, pow_two, mul_assoc] using hb

def zeroCode (x : Coordinates) : ℤ × ℤ × ℤ × ℤ × ℤ :=
  (x.base, x.d1, x.l1, x.u, x.a)

theorem zeroCode_inj {x y : Coordinates} (hnx : numerator x = 0)
    (hny : numerator y = 0) (hl : x.l3 ≠ 0)
    (hc : zeroCode x = zeroCode y) (h3 : x.l3 = y.l3) : x = y := by
  simp only [zeroCode, Prod.mk.injEq] at hc
  have hd : x.d2 = y.d2 := mul_right_cancel₀ hl (by
    dsimp [numerator] at hnx hny
    rw [← hc.2.1, ← hc.2.2.1, ← h3] at hny
    omega)
  cases x; cases y
  simp_all

theorem count_zero_rectangle (K L W V D : ℕ) (hL : 1 ≤ L)
    (U A : Finset ℤ) (S : Finset Coordinates)
    (hS : ∀ x ∈ S, Bounded K L W V x) (hn : ∀ x ∈ S, numerator x = 0)
    (hUA : ∀ x ∈ S, x.u ∈ U ∧ x.a ∈ A)
    (hD : DivisorBound L (2 * W) D) :
    S.card ≤ (baseSet K).card * (differenceSet W).card * (radialSet L).card * U.card * A.card * D := by
  let T := baseSet K ×ˢ differenceSet W ×ˢ radialSet L ×ˢ U ×ˢ A
  have hb : S.card ≤ T.card * D := by
    apply card_le_fibers S T zeroCode D
    · intro x hx
      exact mem_product.mpr ⟨(hS x hx).base_mem, mem_product.mpr ⟨(hS x hx).d1_mem,
        mem_product.mpr ⟨(hS x hx).l1_mem, mem_product.mpr (hUA x hx)⟩⟩⟩
    · intro y hy
      let F := S.filter (fun x => zeroCode x = y)
      by_cases hF : F.Nonempty
      · obtain ⟨x₀, hx₀⟩ := hF
        have hx₀S := (mem_filter.mp hx₀).1
        have hmap : Set.MapsTo Coordinates.l3 (F : Set Coordinates)
            (divisorsIn L (x₀.d1 * x₀.l1) : Set ℤ) := by
          intro x hx
          have hxS := (mem_filter.mp hx).1
          have hc := (mem_filter.mp hx).2.trans (mem_filter.mp hx₀).2.symm
          simp only [zeroCode, Prod.mk.injEq] at hc
          have hl := (hS x hxS).l3_mem
          simp only [radialSet, mem_Ico] at hl
          change x.l3 ∈ divisorsIn L (x₀.d1 * x₀.l1)
          refine mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩, ⟨-x.d2, ?_⟩⟩
          have he := hn x hxS
          dsimp [numerator] at he
          rw [← hc.2.1, ← hc.2.2.1]
          nlinarith
        have hinj : Set.InjOn Coordinates.l3 (F : Set Coordinates) := by
          intro x hx z hz hl
          exact zeroCode_inj (hn x (mem_filter.mp hx).1) (hn z (mem_filter.mp hz).1)
            (ne_of_gt ((hS x (mem_filter.mp hx).1).l3_pos hL))
            ((mem_filter.mp hx).2.trans (mem_filter.mp hz).2.symm) hl
        have hp0 : x₀.d1 * x₀.l1 ≠ 0 := mul_ne_zero (hS x₀ hx₀S).d1_ne
          (ne_of_gt ((hS x₀ hx₀S).l1_pos hL))
        have hp := (hS x₀ hx₀S).abs_product
        have hbound : |x₀.d1 * x₀.l1| ≤ 2 * (L : ℤ) * (2 * W : ℕ) := by
          push_cast
          nlinarith [mul_nonneg (Nat.cast_nonneg L : (0 : ℤ) ≤ L) (Nat.cast_nonneg W : (0 : ℤ) ≤ W)]
        exact (card_le_card_of_injOn Coordinates.l3 hmap hinj).trans
          (hD (x₀.d1 * x₀.l1) hp0 hbound)
      · change F.card ≤ D
        simp [not_nonempty_iff_eq_empty.mp hF]
  simpa [T, card_product, mul_assoc] using hb

theorem count_coordinates (K L W V D : ℕ) (hL : 1 ≤ L)
    (S : Finset Coordinates) (hS : ∀ x ∈ S, Bounded K L W V x)
    (hD : DivisorBound L (2 * W) D) :
    S.card ≤ K * (2 * W + 1) ^ 2 * L ^ 2 * D +
      K * (2 * W + 1) * L * ((2 * L + 1) + (2 * V + 1)) * D := by
  let N := S.filter (fun x => numerator x ≠ 0)
  let ZU := S.filter (fun x => numerator x = 0 ∧ x.u = 0)
  let ZA := S.filter (fun x => numerator x = 0 ∧ x.a = 0)
  have hsub : S ⊆ N ∪ ZU ∪ ZA := by
    intro x hx
    by_cases hn : numerator x = 0
    · have he := (hS x hx).eqn
      simp only [equation, hn, neg_zero, mul_eq_zero] at he
      rcases he with hu | ha
      · simp [N, ZU, ZA, hx, hn, hu]
      · simp [N, ZU, ZA, hx, hn, ha]
    · simp [N, hx, hn]
  have hc := (card_le_card hsub).trans ((card_union_le _ _).trans
    (add_le_add_left (card_union_le _ _) _))
  have hN := count_nonzero K L W V D N
    (fun x hx => hS x (mem_filter.mp hx).1) (fun x hx => (mem_filter.mp hx).2) hD
  have hZU := count_zero_rectangle K L W V D hL {0} (differenceSet L) ZU
    (fun x hx => hS x (mem_filter.mp hx).1) (fun x hx => (mem_filter.mp hx).2.1)
    (fun x hx => ⟨mem_singleton.mpr (mem_filter.mp hx).2.2, (hS x (mem_filter.mp hx).1).a_mem⟩) hD
  have hZA := count_zero_rectangle K L W V D hL (differenceSet V) {0} ZA
    (fun x hx => hS x (mem_filter.mp hx).1) (fun x hx => (mem_filter.mp hx).2.1)
    (fun x hx => ⟨(hS x (mem_filter.mp hx).1).u_mem, mem_singleton.mpr (mem_filter.mp hx).2.2⟩) hD
  have hbase : (baseSet K).card = K := by simp [baseSet]; omega
  have hrad : (radialSet L).card = L := by simp [radialSet]; omega
  have hdiff (B : ℕ) : (differenceSet B).card = 2 * B + 1 := by
    simp [differenceSet]; omega
  rw [hbase, hrad, hdiff] at hN
  simp only [hbase, hrad, hdiff, card_singleton, mul_one] at hZU hZA
  calc
    _ ≤ N.card + ZU.card + ZA.card := hc
    _ ≤ _ := add_le_add (add_le_add hN hZU) hZA
    _ = _ := by ring

theorem count_coordinates_simple (K L W V D : ℕ) (hL : 1 ≤ L) (hW : 1 ≤ W)
    (hV : 1 ≤ V) (S : Finset Coordinates) (hS : ∀ x ∈ S, Bounded K L W V x)
    (hD : DivisorBound L (2 * W) D) :
    S.card ≤ 18 * K * D * (W ^ 2 * L ^ 2 + V * W * L) := by
  have hb := count_coordinates K L W V D hL S hS hD
  have hw : 2 * W + 1 ≤ 3 * W := by omega
  have hl : 2 * L + 1 ≤ 3 * L := by omega
  have hv : 2 * V + 1 ≤ 3 * V := by omega
  have hW2 : W ≤ W ^ 2 := by nlinarith
  calc
    S.card ≤ _ := hb
    _ ≤ K * (3 * W) ^ 2 * L ^ 2 * D + K * (3 * W) * L * (3 * L + 3 * V) * D := by gcongr
    _ = 9 * K * D * (W ^ 2 * L ^ 2 + W * L ^ 2 + V * W * L) := by ring
    _ ≤ 9 * K * D * (W ^ 2 * L ^ 2 + W ^ 2 * L ^ 2 + V * W * L) := by gcongr
    _ ≤ _ := by nlinarith [Nat.zero_le (9 * K * D * (V * W * L))]

abbrev Quadruple := CircleDivisor.SpacingCount.Quadruple

def firstEquation (x : Quadruple) : Prop := x.l1 - x.l2 + x.l3 - x.l4 = 0
def secondEquation (x : Quadruple) : Prop :=
  x.k1 * x.l1 - x.k2 * x.l2 + x.k3 * x.l3 - x.k4 * x.l4 = 0
def coordinates (x : Quadruple) : Coordinates :=
  ⟨x.k4, x.k1 - x.k2, x.k3 - x.k4, x.k2 - x.k4, x.l1 - x.l2, x.l1, x.l3⟩
def reconstruct (x : Coordinates) : Quadruple :=
  ⟨x.base + x.u + x.d1, x.base + x.u, x.base + x.d2, x.base,
    x.l1, x.l1 - x.a, x.l3, x.l3 + x.a⟩

theorem reconstruct_coordinates (x : Quadruple) (h : firstEquation x) :
    reconstruct (coordinates x) = x := by
  cases x
  simp_all [firstEquation, coordinates, reconstruct]
  omega

theorem factorization (x : Quadruple) (h : firstEquation x) :
    secondEquation x ↔ equation (coordinates x) := by
  dsimp [firstEquation] at h
  dsimp [secondEquation, equation, coordinates, numerator]
  have hm := congrArg (fun z : ℤ => x.k4 * z) h
  constructor <;> intro he <;> nlinarith

theorem coordinates_injective : Set.InjOn coordinates {x | firstEquation x} := by
  intro x hx y hy hxy
  rw [← reconstruct_coordinates x hx, ← reconstruct_coordinates y hy, hxy]

structure Admissible (K L W V : ℕ) (x : Quadruple) : Prop where
  base_mem : x.k4 ∈ baseSet K
  l1_mem : x.l1 ∈ radialSet L
  l2_mem : x.l2 ∈ radialSet L
  l3_mem : x.l3 ∈ radialSet L
  first : firstEquation x
  second : secondEquation x
  d1_bound : |x.k1 - x.k2| ≤ W
  d2_bound : |x.k3 - x.k4| ≤ W
  u_bound : |x.k2 - x.k4| ≤ V
  d1_ne : x.k1 ≠ x.k2
  d2_ne : x.k3 ≠ x.k4

theorem Admissible.bounded {K L W V : ℕ} {x : Quadruple} (h : Admissible K L W V x) :
    Bounded K L W V (coordinates x) := by
  refine ⟨h.base_mem, ?_, ?_, ?_, ?_, h.l1_mem, h.l3_mem,
    sub_ne_zero.mpr h.d1_ne, sub_ne_zero.mpr h.d2_ne, (factorization x h.first).mp h.second⟩
  · simpa [coordinates, differenceSet, mem_Icc] using abs_le.mp h.d1_bound
  · simpa [coordinates, differenceSet, mem_Icc] using abs_le.mp h.d2_bound
  · simpa [coordinates, differenceSet, mem_Icc] using abs_le.mp h.u_bound
  · have h1 := h.l1_mem
    have h2 := h.l2_mem
    simp only [radialSet, mem_Ico] at h1 h2
    simp only [coordinates, differenceSet, mem_Icc]
    omega

theorem count_quadruples (K L W V D : ℕ) (hL : 1 ≤ L) (hW : 1 ≤ W) (hV : 1 ≤ V)
    (S : Finset Quadruple) (hS : ∀ x ∈ S, Admissible K L W V x)
    (hD : DivisorBound L (2 * W) D) :
    S.card ≤ 18 * K * D * (W ^ 2 * L ^ 2 + V * W * L) := by
  have hi : Set.InjOn coordinates (S : Set Quadruple) := by
    intro x hx y hy hxy
    exact coordinates_injective (hS x hx).first (hS y hy).first hxy
  rw [← card_image_of_injOn hi]
  apply count_coordinates_simple K L W V D hL hW hV
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := mem_image.mp hx
    exact (hS y hy).bounded
  · exact hD

end
end CircleDivisor.EnergyV3.PairedCount
