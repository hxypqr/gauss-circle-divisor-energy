import Mathlib

/-!
# The integer counting step in Lemma 3.2

The proof separates the nonzero product, nontrivial zero product, and the three
remaining nonradial zero-product cases.  All counting statements below concern
actual finite sets of integer configurations. No spacing estimate is an input.
-/

namespace CircleDivisor.SpacingCount

open Finset
noncomputable section

structure Quadruple where
  k1 : ℤ
  k2 : ℤ
  k3 : ℤ
  k4 : ℤ
  l1 : ℤ
  l2 : ℤ
  l3 : ℤ
  l4 : ℤ
  deriving DecidableEq

structure Coordinates where
  base : ℤ
  d1 : ℤ
  d2 : ℤ
  d3 : ℤ
  a : ℤ
  b : ℤ
  radial : ℤ
  deriving DecidableEq

def Quadruple.firstEquation (x : Quadruple) : Prop :=
  x.l1 + x.l2 = x.l3 + x.l4

def Quadruple.secondEquation (x : Quadruple) : Prop :=
  x.k1 * x.l1 + x.k2 * x.l2 = x.k3 * x.l3 + x.k4 * x.l4

def Quadruple.coordinates (x : Quadruple) : Coordinates :=
  ⟨x.k4, x.k1 - x.k4, x.k2 - x.k4, x.k3 - x.k4,
    x.l1 - x.l3, x.l2 - x.l3, x.l3⟩

def Coordinates.reconstruct (x : Coordinates) : Quadruple :=
  ⟨x.base + x.d1, x.base + x.d2, x.base + x.d3, x.base,
    x.radial + x.a, x.radial + x.b, x.radial, x.radial + x.a + x.b⟩

def Coordinates.numerator (x : Coordinates) : ℤ := x.a * x.d1 + x.b * x.d2

def Coordinates.equation (x : Coordinates) : Prop :=
  x.numerator = x.radial * (x.d3 - x.d1 - x.d2)

def Coordinates.nonradial (x : Coordinates) : Prop :=
  ¬ (x.d1 = 0 ∧ x.d2 = 0 ∧ x.d3 = 0)

theorem reconstruct_coordinates (x : Quadruple) (h : x.firstEquation) :
    x.coordinates.reconstruct = x := by
  cases x
  simp_all [Quadruple.firstEquation, Quadruple.coordinates, Coordinates.reconstruct]
  omega

theorem coordinates_reconstruct (x : Coordinates) :
    x.reconstruct.coordinates = x := by
  cases x
  simp [Quadruple.coordinates, Coordinates.reconstruct]

theorem change_variables (x : Quadruple) (h : x.firstEquation) :
    x.secondEquation ↔ x.coordinates.equation := by
  simp only [Quadruple.firstEquation] at h
  simp only [Quadruple.secondEquation, Quadruple.coordinates,
    Coordinates.equation, Coordinates.numerator]
  have hm := congrArg (fun z : ℤ => x.k4 * z) h
  constructor <;> intro h₂ <;> nlinarith [hm]

theorem coordinates_injective :
    Set.InjOn Quadruple.coordinates {x | x.firstEquation} := by
  intro x hx y hy hxy
  rw [← reconstruct_coordinates x hx, ← reconstruct_coordinates y hy, hxy]

theorem numerator_divisible (x : Coordinates) (h : x.equation) :
    x.radial ∣ x.numerator := ⟨x.d3 - x.d1 - x.d2, h⟩

theorem zero_numerator (x : Coordinates) (h : x.equation) (hp : x.radial ≠ 0)
    (hn : x.numerator = 0) : x.d3 = x.d1 + x.d2 := by
  have hz : x.radial * (x.d3 - x.d1 - x.d2) = 0 := h.symm.trans hn
  have := (mul_eq_zero.mp hz).resolve_left hp
  omega

theorem zero_branch_cover (x : Coordinates) (he : x.equation) (hp : x.radial ≠ 0)
    (hnr : x.nonradial) (hn : x.numerator = 0) :
    x.a * x.d1 ≠ 0 ∨ (x.a = 0 ∧ x.b = 0) ∨
      (x.a = 0 ∧ x.d2 = 0) ∨ (x.d1 = 0 ∧ x.b = 0) := by
  by_cases ha : x.a * x.d1 = 0
  · have hb : x.b * x.d2 = 0 := by
      simp only [Coordinates.numerator] at hn
      omega
    rcases mul_eq_zero.mp ha with ha | hd1 <;>
      rcases mul_eq_zero.mp hb with hb | hd2
    · exact .inr (.inl ⟨ha, hb⟩)
    · exact .inr (.inr (.inl ⟨ha, hd2⟩))
    · exact .inr (.inr (.inr ⟨hd1, hb⟩))
    · exfalso
      apply hnr
      have hd3 := zero_numerator x he hp hn
      exact ⟨hd1, hd2, by omega⟩
  · exact .inl ha

private theorem card_le_fibers {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (T : Finset β) (f : α → β) (D : ℕ)
    (hf : ∀ x ∈ S, f x ∈ T)
    (hD : ∀ y ∈ T, (S.filter (fun x => f x = y)).card ≤ D) :
    S.card ≤ T.card * D := by
  calc
    S.card = ∑ y ∈ T, (S.filter (fun x => f x = y)).card :=
      Finset.card_eq_sum_card_fiberwise hf
    _ ≤ ∑ _y ∈ T, D := Finset.sum_le_sum hD
    _ = T.card * D := by simp

def baseSet (K : ℕ) : Finset ℤ := Ico (K : ℤ) (2 * K)
def differenceSet (V : ℕ) : Finset ℤ := Icc (-(V : ℤ)) V
def radialSet (L : ℕ) : Finset ℤ := Ico (L : ℤ) (2 * L)

structure Bounded (K L V : ℕ) (x : Coordinates) : Prop where
  base_mem : x.base ∈ baseSet K
  d1_mem : x.d1 ∈ differenceSet V
  d2_mem : x.d2 ∈ differenceSet V
  d3_mem : x.d3 ∈ differenceSet V
  a_mem : x.a ∈ differenceSet L
  b_mem : x.b ∈ differenceSet L
  radial_mem : x.radial ∈ radialSet L
  equation : x.equation
  nonradial : x.nonradial

theorem Bounded.radial_pos {K L V : ℕ} {x : Coordinates}
    (h : Bounded K L V x) (_hL : 1 ≤ L) : 0 < x.radial := by
  have := h.radial_mem
  simp only [radialSet, mem_Ico] at this
  omega

theorem Bounded.abs_numerator {K L V : ℕ} {x : Coordinates}
    (h : Bounded K L V x) : |x.numerator| ≤ 2 * (L : ℤ) * V := by
  have ha : |x.a| ≤ (L : ℤ) := abs_le.mpr (by simpa [differenceSet] using h.a_mem)
  have hb : |x.b| ≤ (L : ℤ) := abs_le.mpr (by simpa [differenceSet] using h.b_mem)
  have hd1 : |x.d1| ≤ (V : ℤ) := abs_le.mpr (by simpa [differenceSet] using h.d1_mem)
  have hd2 : |x.d2| ≤ (V : ℤ) := abs_le.mpr (by simpa [differenceSet] using h.d2_mem)
  calc
    |x.numerator| ≤ |x.a * x.d1| + |x.b * x.d2| := abs_add_le ..
    _ = |x.a| * |x.d1| + |x.b| * |x.d2| := by rw [abs_mul, abs_mul]
    _ ≤ (L : ℤ) * V + L * V := add_le_add
      (mul_le_mul ha hd1 (abs_nonneg _) (by positivity))
      (mul_le_mul hb hd2 (abs_nonneg _) (by positivity))
    _ = 2 * (L : ℤ) * V := by ring

theorem Bounded.abs_product {K L V : ℕ} {x : Coordinates}
    (h : Bounded K L V x) : |x.a * x.d1| ≤ 2 * (L : ℤ) * V := by
  have ha : |x.a| ≤ (L : ℤ) := abs_le.mpr (by simpa [differenceSet] using h.a_mem)
  have hd : |x.d1| ≤ (V : ℤ) := abs_le.mpr (by simpa [differenceSet] using h.d1_mem)
  rw [abs_mul]
  have := mul_le_mul ha hd (abs_nonneg _) (by positivity : (0 : ℤ) ≤ L)
  nlinarith [mul_nonneg (Nat.cast_nonneg L : (0 : ℤ) ≤ L)
    (Nat.cast_nonneg V : (0 : ℤ) ≤ V)]

/-- Signed divisors in a fixed finite interval, including every radial value
and every difference used below. The zero dividend is expressly excluded in
the divisor-bound hypothesis. -/
def divisorsIn (L : ℕ) (n : ℤ) : Finset ℤ :=
  (Icc (-(2 * (L : ℤ))) (2 * L)).filter (fun d => d ∣ n)

def DivisorBound (L V D : ℕ) : Prop :=
  ∀ n : ℤ, n ≠ 0 → |n| ≤ 2 * (L : ℤ) * V → (divisorsIn L n).card ≤ D

private def code5 (x : Coordinates) : ℤ × ℤ × ℤ × ℤ × ℤ :=
  (x.base, x.d1, x.d2, x.a, x.b)

private theorem eq_of_code5_radial {x y : Coordinates}
    (hx : x.equation) (hy : y.equation) (hr : x.radial ≠ 0)
    (hc : code5 x = code5 y) (hl : x.radial = y.radial) : x = y := by
  simp only [code5, Prod.mk.injEq] at hc
  rcases hc with ⟨hbase, hd1, hd2, ha, hb⟩
  have heq : x.radial * (x.d3 - x.d1 - x.d2) =
      x.radial * (y.d3 - x.d1 - x.d2) := by
    have hx' := hx
    have hy' := hy
    simp only [Coordinates.equation, Coordinates.numerator, ← hl, ← hd1, ← hd2,
      ← ha, ← hb] at hx' hy'
    exact hx'.symm.trans hy'
  have hd3 : x.d3 = y.d3 := by
    have := mul_left_cancel₀ hr heq
    omega
  cases x
  cases y
  simp_all

private def code5Set (K L V : ℕ) :=
  baseSet K ×ˢ differenceSet V ×ˢ differenceSet V ×ˢ
    differenceSet L ×ˢ differenceSet L

private theorem code5_mem {K L V : ℕ} {x : Coordinates} (h : Bounded K L V x) :
    code5 x ∈ code5Set K L V := by
  simpa only [code5, code5Set, mem_product] using
    And.intro h.base_mem (And.intro h.d1_mem (And.intro h.d2_mem
      (And.intro h.a_mem h.b_mem)))

theorem count_nonzero_numerator (K L V D : ℕ) (hL : 1 ≤ L)
    (S : Finset Coordinates) (hS : ∀ x ∈ S, Bounded K L V x)
    (hn : ∀ x ∈ S, x.numerator ≠ 0) (hD : DivisorBound L V D) :
    S.card ≤ (baseSet K).card * (differenceSet V).card ^ 2 *
      (differenceSet L).card ^ 2 * D := by
  have hcount : S.card ≤ (code5Set K L V).card * D := by
    apply card_le_fibers S (code5Set K L V) code5 D
    · intro x hx
      exact code5_mem (hS x hx)
    · intro y _hy
      let F := S.filter (fun x => code5 x = y)
      by_cases hF : F.Nonempty
      · obtain ⟨x₀, hx₀⟩ := hF
        have hx₀S : x₀ ∈ S := (mem_filter.mp hx₀).1
        have hx₀c : code5 x₀ = y := (mem_filter.mp hx₀).2
        have hinj : Set.InjOn Coordinates.radial (F : Set Coordinates) := by
          intro x hx z hz hrad
          have hxS := (mem_filter.mp hx).1
          have hzS := (mem_filter.mp hz).1
          exact eq_of_code5_radial (hS x hxS).equation (hS z hzS).equation
            (ne_of_gt ((hS x hxS).radial_pos hL))
            ((mem_filter.mp hx).2.trans (mem_filter.mp hz).2.symm) hrad
        have hmap : Set.MapsTo Coordinates.radial (F : Set Coordinates)
            (divisorsIn L x₀.numerator : Set ℤ) := by
          intro x hx
          have hxS := (mem_filter.mp hx).1
          have hc : code5 x = code5 x₀ := (mem_filter.mp hx).2.trans hx₀c.symm
          have hnum : x.numerator = x₀.numerator := by
            simp only [code5, Prod.mk.injEq] at hc
            simp [Coordinates.numerator, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2]
          have hl := (hS x hxS).radial_mem
          simp only [radialSet, mem_Ico] at hl
          change x.radial ∈ divisorsIn L x₀.numerator
          simp only [divisorsIn, mem_filter, mem_Icc]
          exact ⟨⟨by omega, by omega⟩, hnum ▸ numerator_divisible x (hS x hxS).equation⟩
        exact (card_le_card_of_injOn Coordinates.radial hmap hinj).trans
          (hD x₀.numerator (hn x₀ hx₀S) (hS x₀ hx₀S).abs_numerator)
      · have hz : F = ∅ := not_nonempty_iff_eq_empty.mp hF
        change F.card ≤ D
        simp [hz]
  simpa [code5Set, card_product, pow_two, mul_assoc] using hcount

private def code4 (x : Coordinates) : ℤ × ℤ × ℤ × ℤ :=
  (x.base, x.d1, x.a, x.radial)

private def code4Set (K L V : ℕ) :=
  baseSet K ×ˢ differenceSet V ×ˢ differenceSet L ×ˢ radialSet L

private theorem eq_of_code4_b {x y : Coordinates}
    (hx : x.equation) (hy : y.equation) (hr : x.radial ≠ 0)
    (hnx : x.numerator = 0) (hny : y.numerator = 0) (ha : x.a * x.d1 ≠ 0)
    (hc : code4 x = code4 y) (hb : x.b = y.b) : x = y := by
  simp only [code4, Prod.mk.injEq] at hc
  rcases hc with ⟨hbase, hd1, ha', hl⟩
  have hb0 : x.b ≠ 0 := by
    intro hz
    apply ha
    simpa [Coordinates.numerator, hz] using hnx
  have hmul : x.b * x.d2 = x.b * y.d2 := by
    simp only [Coordinates.numerator] at hnx hny
    rw [← ha', ← hd1, ← hb] at hny
    omega
  have hd2 : x.d2 = y.d2 := mul_left_cancel₀ hb0 hmul
  apply eq_of_code5_radial hx hy hr _ hl
  simp [code5, hbase, hd1, hd2, ha', hb]

theorem count_nontrivial_zero (K L V D : ℕ) (hL : 1 ≤ L)
    (S : Finset Coordinates) (hS : ∀ x ∈ S, Bounded K L V x)
    (hn : ∀ x ∈ S, x.numerator = 0)
    (hp : ∀ x ∈ S, x.a * x.d1 ≠ 0) (hD : DivisorBound L V D) :
    S.card ≤ (baseSet K).card * (differenceSet V).card *
      (differenceSet L).card * (radialSet L).card * D := by
  have hcount : S.card ≤ (code4Set K L V).card * D := by
    apply card_le_fibers S (code4Set K L V) code4 D
    · intro x hx
      have h := hS x hx
      simpa [code4, code4Set] using
        And.intro h.base_mem (And.intro h.d1_mem (And.intro h.a_mem h.radial_mem))
    · intro y _hy
      let F := S.filter (fun x => code4 x = y)
      by_cases hF : F.Nonempty
      · obtain ⟨x₀, hx₀⟩ := hF
        have hx₀S : x₀ ∈ S := (mem_filter.mp hx₀).1
        have hx₀c : code4 x₀ = y := (mem_filter.mp hx₀).2
        have hinj : Set.InjOn Coordinates.b (F : Set Coordinates) := by
          intro x hx z hz hb
          have hxS := (mem_filter.mp hx).1
          have hzS := (mem_filter.mp hz).1
          exact eq_of_code4_b (hS x hxS).equation (hS z hzS).equation
            (ne_of_gt ((hS x hxS).radial_pos hL)) (hn x hxS) (hn z hzS) (hp x hxS)
            ((mem_filter.mp hx).2.trans (mem_filter.mp hz).2.symm) hb
        have hmap : Set.MapsTo Coordinates.b (F : Set Coordinates)
            (divisorsIn L (x₀.a * x₀.d1) : Set ℤ) := by
          intro x hx
          have hxS := (mem_filter.mp hx).1
          have hc : code4 x = code4 x₀ := (mem_filter.mp hx).2.trans hx₀c.symm
          simp only [code4, Prod.mk.injEq] at hc
          have hprod : x.a * x.d1 = x₀.a * x₀.d1 := by rw [hc.2.1, hc.2.2.1]
          have hb := (hS x hxS).b_mem
          simp only [differenceSet, mem_Icc] at hb
          change x.b ∈ divisorsIn L (x₀.a * x₀.d1)
          simp only [divisorsIn, mem_filter, mem_Icc]
          refine ⟨⟨by omega, by omega⟩, ?_⟩
          refine ⟨-x.d2, ?_⟩
          have hn' := hn x hxS
          simp only [Coordinates.numerator] at hn'
          rw [← hprod]
          nlinarith
        exact (card_le_card_of_injOn Coordinates.b hmap hinj).trans
          (hD (x₀.a * x₀.d1) (hp x₀ hx₀S) (hS x₀ hx₀S).abs_product)
      · have hz : F = ∅ := not_nonempty_iff_eq_empty.mp hF
        change F.card ≤ D
        simp [hz]
  simpa [code4Set, card_product, mul_assoc] using hcount

private def code6 (x : Coordinates) : ℤ × ℤ × ℤ × ℤ × ℤ × ℤ :=
  (x.base, x.d1, x.d2, x.a, x.b, x.radial)

/-- A box count on the solution surface; the equation uniquely recovers d3. -/
theorem count_rectangle (S : Finset Coordinates) (B D₁ D₂ A B' R : Finset ℤ)
    (he : ∀ x ∈ S, x.equation) (hp : ∀ x ∈ S, x.radial ≠ 0)
    (hb : ∀ x ∈ S, x.base ∈ B ∧ x.d1 ∈ D₁ ∧ x.d2 ∈ D₂ ∧
      x.a ∈ A ∧ x.b ∈ B' ∧ x.radial ∈ R) :
    S.card ≤ B.card * D₁.card * D₂.card * A.card * B'.card * R.card := by
  have hi : Set.InjOn code6 (S : Set Coordinates) := by
    intro x hx y hy hc
    simp only [code6, Prod.mk.injEq] at hc
    apply eq_of_code5_radial (he x hx) (he y hy) (hp x hx) _ hc.2.2.2.2.2
    simp only [code5, Prod.mk.injEq]
    exact ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2.1⟩
  have hm : Set.MapsTo code6 (S : Set Coordinates)
      (↑(B ×ˢ D₁ ×ˢ D₂ ×ˢ A ×ˢ B' ×ˢ R) : Set (ℤ × ℤ × ℤ × ℤ × ℤ × ℤ)) := by
    intro x hx
    change code6 x ∈ B ×ˢ D₁ ×ˢ D₂ ×ˢ A ×ˢ B' ×ˢ R
    simpa only [code6, mem_product] using hb x hx
  simpa [card_product, mul_assoc] using card_le_card_of_injOn code6 hm hi

theorem count_zero_a_b (K L V : ℕ) (hL : 1 ≤ L)
    (S : Finset Coordinates) (hS : ∀ x ∈ S, Bounded K L V x)
    (hz : ∀ x ∈ S, x.a = 0 ∧ x.b = 0) :
    S.card ≤ (baseSet K).card * (differenceSet V).card ^ 2 * (radialSet L).card := by
  have h := count_rectangle S (baseSet K) (differenceSet V) (differenceSet V)
    {0} {0} (radialSet L) (fun x hx => (hS x hx).equation)
    (fun x hx => ne_of_gt ((hS x hx).radial_pos hL)) (by
      intro x hx
      have hb := hS x hx
      exact ⟨hb.base_mem, hb.d1_mem, hb.d2_mem, by simpa using (hz x hx).1,
        by simpa using (hz x hx).2, hb.radial_mem⟩)
  simpa [pow_two, mul_assoc] using h

theorem count_zero_a_d2 (K L V : ℕ) (hL : 1 ≤ L)
    (S : Finset Coordinates) (hS : ∀ x ∈ S, Bounded K L V x)
    (hz : ∀ x ∈ S, x.a = 0 ∧ x.d2 = 0) :
    S.card ≤ (baseSet K).card * (differenceSet V).card *
      (differenceSet L).card * (radialSet L).card := by
  have h := count_rectangle S (baseSet K) (differenceSet V) {0}
    {0} (differenceSet L) (radialSet L) (fun x hx => (hS x hx).equation)
    (fun x hx => ne_of_gt ((hS x hx).radial_pos hL)) (by
      intro x hx
      have hb := hS x hx
      exact ⟨hb.base_mem, hb.d1_mem, by simpa using (hz x hx).2,
        by simpa using (hz x hx).1, hb.b_mem, hb.radial_mem⟩)
  simpa [mul_assoc] using h

theorem count_zero_d1_b (K L V : ℕ) (hL : 1 ≤ L)
    (S : Finset Coordinates) (hS : ∀ x ∈ S, Bounded K L V x)
    (hz : ∀ x ∈ S, x.d1 = 0 ∧ x.b = 0) :
    S.card ≤ (baseSet K).card * (differenceSet V).card *
      (differenceSet L).card * (radialSet L).card := by
  have h := count_rectangle S (baseSet K) {0} (differenceSet V)
    (differenceSet L) {0} (radialSet L) (fun x hx => (hS x hx).equation)
    (fun x hx => ne_of_gt ((hS x hx).radial_pos hL)) (by
      intro x hx
      have hb := hS x hx
      exact ⟨hb.base_mem, by simpa using (hz x hx).1, hb.d2_mem,
        hb.a_mem, by simpa using (hz x hx).2, hb.radial_mem⟩)
  simpa [mul_assoc] using h

@[simp] theorem card_baseSet (K : ℕ) : (baseSet K).card = K := by
  rw [baseSet, Int.card_Ico]
  have h : 2 * (K : ℤ) - K = K := by ring
  rw [h, Int.toNat_natCast]

@[simp] theorem card_radialSet (L : ℕ) : (radialSet L).card = L :=
  card_baseSet L

@[simp] theorem card_differenceSet (V : ℕ) : (differenceSet V).card = 2 * V + 1 := by
  rw [differenceSet, Int.card_Icc]
  have h : (V : ℤ) + 1 - -(V : ℤ) = ↑(2 * V + 1) := by push_cast; ring
  rw [h, Int.toNat_natCast]

/-- The complete, quantitative finite-set bound underlying Lemma 3.2.
`D` bounds only the elementary multiplicity of integer divisors. -/
theorem count_coordinates (K L V D : ℕ) (hL : 1 ≤ L)
    (S : Finset Coordinates) (hS : ∀ x ∈ S, Bounded K L V x)
    (hD : DivisorBound L V D) :
    S.card ≤ K * (2 * V + 1) ^ 2 * (2 * L + 1) ^ 2 * D +
      K * (2 * V + 1) * (2 * L + 1) * L * D +
      K * (2 * V + 1) ^ 2 * L + 2 * (K * (2 * V + 1) * (2 * L + 1) * L) := by
  classical
  let S₀ := S.filter (fun x => x.numerator ≠ 0)
  let S₁ := S.filter (fun x => x.numerator = 0 ∧ x.a * x.d1 ≠ 0)
  let S₂ := S.filter (fun x => x.a = 0 ∧ x.b = 0)
  let S₃ := S.filter (fun x => x.a = 0 ∧ x.d2 = 0)
  let S₄ := S.filter (fun x => x.d1 = 0 ∧ x.b = 0)
  have h₀ : S₀.card ≤ K * (2 * V + 1) ^ 2 * (2 * L + 1) ^ 2 * D := by
    simpa using count_nonzero_numerator K L V D hL S₀
      (fun x hx => hS x (mem_filter.mp hx).1) (fun _ hx => (mem_filter.mp hx).2) hD
  have h₁ : S₁.card ≤ K * (2 * V + 1) * (2 * L + 1) * L * D := by
    simpa using count_nontrivial_zero K L V D hL S₁
      (fun x hx => hS x (mem_filter.mp hx).1) (fun _ hx => (mem_filter.mp hx).2.1)
      (fun _ hx => (mem_filter.mp hx).2.2) hD
  have h₂ : S₂.card ≤ K * (2 * V + 1) ^ 2 * L := by
    simpa using count_zero_a_b K L V hL S₂
      (fun x hx => hS x (mem_filter.mp hx).1) (fun _ hx => (mem_filter.mp hx).2)
  have h₃ : S₃.card ≤ K * (2 * V + 1) * (2 * L + 1) * L := by
    simpa using count_zero_a_d2 K L V hL S₃
      (fun x hx => hS x (mem_filter.mp hx).1) (fun _ hx => (mem_filter.mp hx).2)
  have h₄ : S₄.card ≤ K * (2 * V + 1) * (2 * L + 1) * L := by
    simpa using count_zero_d1_b K L V hL S₄
      (fun x hx => hS x (mem_filter.mp hx).1) (fun _ hx => (mem_filter.mp hx).2)
  have hsub : S ⊆ S₀ ∪ S₁ ∪ S₂ ∪ S₃ ∪ S₄ := by
    intro x hx
    by_cases hn : x.numerator = 0
    · have h := hS x hx
      rcases zero_branch_cover x h.equation (ne_of_gt (h.radial_pos hL)) h.nonradial hn
        with hp | hab | had | hdb
      · simp only [mem_union]
        exact .inl (.inl (.inl (.inr (mem_filter.mpr ⟨hx, hn, hp⟩))))
      · simp only [mem_union]
        exact .inl (.inl (.inr (mem_filter.mpr ⟨hx, hab⟩)))
      · simp only [mem_union]
        exact .inl (.inr (mem_filter.mpr ⟨hx, had⟩))
      · simp only [mem_union]
        exact .inr (mem_filter.mpr ⟨hx, hdb⟩)
    · simp only [mem_union]
      exact .inl (.inl (.inl (.inl (mem_filter.mpr ⟨hx, hn⟩))))
  have hc := card_le_card hsub
  have hc₀ := card_union_le S₀ S₁
  have hc₁ := card_union_le (S₀ ∪ S₁) S₂
  have hc₂ := card_union_le (S₀ ∪ S₁ ∪ S₂) S₃
  have hc₃ := card_union_le (S₀ ∪ S₁ ∪ S₂ ∪ S₃) S₄
  omega

/-- A convenient absolute constant version. -/
theorem count_coordinates_simple (K L V D : ℕ) (hL : 1 ≤ L) (hV : 1 ≤ V)
    (hDpos : 1 ≤ D) (S : Finset Coordinates) (hS : ∀ x ∈ S, Bounded K L V x)
    (hD : DivisorBound L V D) :
    S.card ≤ 117 * K * V ^ 2 * L ^ 2 * D := by
  have hVL : V ≤ V ^ 2 := by nlinarith
  have hLL : L ≤ L ^ 2 := by nlinarith
  have hV3 : 2 * V + 1 ≤ 3 * V := by omega
  have hL3 : 2 * L + 1 ≤ 3 * L := by omega
  have h₀ : K * (2 * V + 1) ^ 2 * (2 * L + 1) ^ 2 * D ≤
      81 * K * V ^ 2 * L ^ 2 * D := by
    calc
      _ ≤ K * (3 * V) ^ 2 * (3 * L) ^ 2 * D := by gcongr
      _ = _ := by ring
  have h₁ : K * (2 * V + 1) * (2 * L + 1) * L * D ≤
      9 * K * V ^ 2 * L ^ 2 * D := by
    calc
      _ ≤ K * (3 * V) * (3 * L) * L * D := by gcongr
      _ = 9 * K * V * L ^ 2 * D := by ring
      _ ≤ _ := by gcongr
  have h₂ : K * (2 * V + 1) ^ 2 * L ≤ 9 * K * V ^ 2 * L ^ 2 * D := by
    calc
      _ ≤ K * (3 * V) ^ 2 * L := by gcongr
      _ = 9 * K * V ^ 2 * L := by ring
      _ ≤ 9 * K * V ^ 2 * L ^ 2 := by gcongr
      _ ≤ 9 * K * V ^ 2 * L ^ 2 * D := Nat.le_mul_of_pos_right _ (by omega)
  have h₃ : K * (2 * V + 1) * (2 * L + 1) * L ≤
      9 * K * V ^ 2 * L ^ 2 * D := by
    calc
      _ ≤ K * (3 * V) * (3 * L) * L := by gcongr
      _ = 9 * K * V * L ^ 2 := by ring
      _ ≤ 9 * K * V ^ 2 * L ^ 2 := by gcongr
      _ ≤ 9 * K * V ^ 2 * L ^ 2 * D := Nat.le_mul_of_pos_right _ (by omega)
  have hc := count_coordinates K L V D hL S hS hD
  nlinarith

/-- A finite divisor maximum. The zero dividend is omitted, since its infinite
divisor family is precisely the exceptional case treated separately. -/
def divisorMaximum (L V : ℕ) : ℕ := 1 +
  (Icc (-(2 * (L : ℤ) * V)) (2 * (L : ℤ) * V)).sup
    (fun n => if n = 0 then 0 else (divisorsIn L n).card)

theorem divisorMaximum_pos (L V : ℕ) : 1 ≤ divisorMaximum L V := by
  unfold divisorMaximum
  omega

theorem divisorMaximum_bound (L V : ℕ) : DivisorBound L V (divisorMaximum L V) := by
  intro n hn habs
  have hm : n ∈ Icc (-(2 * (L : ℤ) * V)) (2 * (L : ℤ) * V) :=
    mem_Icc.mpr (abs_le.mp habs)
  have h := Finset.le_sup (f := fun n => if n = 0 then 0 else (divisorsIn L n).card) hm
  simp only [if_neg hn] at h
  unfold divisorMaximum
  omega

/-- The radius condition about k4 is weaker than the diameter condition in the
manuscript, so the bound proved for this set also covers its stated set. -/
structure Admissible (K L V : ℕ) (x : Quadruple) : Prop where
  k1_mem : x.k1 ∈ baseSet K
  k2_mem : x.k2 ∈ baseSet K
  k3_mem : x.k3 ∈ baseSet K
  k4_mem : x.k4 ∈ baseSet K
  l1_mem : x.l1 ∈ radialSet L
  l2_mem : x.l2 ∈ radialSet L
  l3_mem : x.l3 ∈ radialSet L
  l4_mem : x.l4 ∈ radialSet L
  d1_mem : x.k1 - x.k4 ∈ differenceSet V
  d2_mem : x.k2 - x.k4 ∈ differenceSet V
  d3_mem : x.k3 - x.k4 ∈ differenceSet V
  first : x.firstEquation
  second : x.secondEquation
  nonradial : ¬ (x.k1 = x.k4 ∧ x.k2 = x.k4 ∧ x.k3 = x.k4)

theorem Admissible.bounded {K L V : ℕ} {x : Quadruple} (h : Admissible K L V x) :
    Bounded K L V x.coordinates := by
  refine ⟨h.k4_mem, h.d1_mem, h.d2_mem, h.d3_mem, ?_, ?_, h.l3_mem,
    (change_variables x h.first).mp h.second, ?_⟩
  · have h₁ := h.l1_mem
    have h₃ := h.l3_mem
    simp only [radialSet, mem_Ico] at h₁ h₃
    simp only [Quadruple.coordinates, differenceSet, mem_Icc]
    omega
  · have h₂ := h.l2_mem
    have h₃ := h.l3_mem
    simp only [radialSet, mem_Ico] at h₂ h₃
    simp only [Quadruple.coordinates, differenceSet, mem_Icc]
    omega
  · simp only [Coordinates.nonradial, Quadruple.coordinates]
    intro he
    apply h.nonradial
    omega

/-- Lemma 3.2 for any finite set of original integer quadruples, with the divisor
multiplicity exposed as the only remaining elementary number-theory input. -/
theorem count_quadruples (K L V D : ℕ) (hL : 1 ≤ L) (hV : 1 ≤ V)
    (hDpos : 1 ≤ D) (S : Finset Quadruple) (hS : ∀ x ∈ S, Admissible K L V x)
    (hD : DivisorBound L V D) :
    S.card ≤ 117 * K * V ^ 2 * L ^ 2 * D := by
  have hcard : (S.image Quadruple.coordinates).card = S.card := by
    apply card_image_of_injOn
    exact coordinates_injective.mono (fun x hx => (hS x hx).first)
  rw [← hcard]
  apply count_coordinates_simple K L V D hL hV hDpos _ _ hD
  intro y hy
  obtain ⟨x, hx, rfl⟩ := mem_image.mp hy
  exact (hS x hx).bounded

def allQuadruples (K L : ℕ) : Finset Quadruple :=
  (baseSet K).biUnion fun k1 => (baseSet K).biUnion fun k2 =>
    (baseSet K).biUnion fun k3 => (baseSet K).biUnion fun k4 =>
    (radialSet L).biUnion fun l1 => (radialSet L).biUnion fun l2 =>
    (radialSet L).biUnion fun l3 => (radialSet L).image fun l4 =>
      ⟨k1, k2, k3, k4, l1, l2, l3, l4⟩

def admissibleQuadruples (K L V : ℕ) : Finset Quadruple := by
  classical
  exact (allQuadruples K L).filter (Admissible K L V)

theorem mem_allQuadruples {K L : ℕ} {x : Quadruple} :
    x ∈ allQuadruples K L ↔
      x.k1 ∈ baseSet K ∧ x.k2 ∈ baseSet K ∧ x.k3 ∈ baseSet K ∧ x.k4 ∈ baseSet K ∧
      x.l1 ∈ radialSet L ∧ x.l2 ∈ radialSet L ∧ x.l3 ∈ radialSet L ∧ x.l4 ∈ radialSet L := by
  cases x
  simp [allQuadruples]

theorem mem_admissibleQuadruples {K L V : ℕ} {x : Quadruple} :
    x ∈ admissibleQuadruples K L V ↔ Admissible K L V x := by
  classical
  simp only [admissibleQuadruples, mem_filter]
  constructor
  · exact And.right
  · intro h
    exact ⟨mem_allQuadruples.mpr ⟨h.k1_mem, h.k2_mem, h.k3_mem, h.k4_mem,
      h.l1_mem, h.l2_mem, h.l3_mem, h.l4_mem⟩, h⟩

/-- Fully unconditional finite counting theorem: no analytic or arithmetic
assumptions occur in this statement. -/
theorem lemma_3_2_finite (K L V : ℕ) (hL : 1 ≤ L) (hV : 1 ≤ V) :
    (admissibleQuadruples K L V).card ≤
      117 * K * V ^ 2 * L ^ 2 * divisorMaximum L V := by
  exact count_quadruples K L V (divisorMaximum L V) hL hV (divisorMaximum_pos L V)
    _ (fun _ hx => mem_admissibleQuadruples.mp hx) (divisorMaximum_bound L V)

private def signedCode (d : ℤ) : ℕ × Bool := (d.natAbs, decide (d < 0))

private theorem signedCode_injective : Function.Injective signedCode := by
  intro d e he
  have ha : d.natAbs = e.natAbs := congrArg Prod.fst he
  have hs : decide (d < 0) = decide (e < 0) := congrArg Prod.snd he
  have hs' : (d < 0 ↔ e < 0) := by simpa using hs
  rcases Int.natAbs_eq_natAbs_iff.mp ha with h | h
  · exact h
  · omega

/-- The finite divisor input above is bounded by twice the usual positive
divisor function. This explicitly links it to the classical divisor estimate. -/
theorem card_divisorsIn_le (L : ℕ) (n : ℤ) (hn : n ≠ 0) :
    (divisorsIn L n).card ≤ 2 * n.natAbs.divisors.card := by
  have hmap : Set.MapsTo signedCode (divisorsIn L n : Set ℤ)
      (↑(n.natAbs.divisors ×ˢ (univ : Finset Bool)) : Set (ℕ × Bool)) := by
    intro d hd
    change signedCode d ∈ n.natAbs.divisors ×ˢ (univ : Finset Bool)
    simp only [signedCode, mem_product, mem_univ, and_true]
    have hdvd : d ∣ n := (mem_filter.mp hd).2
    exact Nat.mem_divisors.mpr ⟨Int.natAbs_dvd_natAbs.mpr hdvd, by simpa using hn⟩
  have h := card_le_card_of_injOn signedCode hmap signedCode_injective.injOn
  simpa [card_product, mul_comm] using h

/-- This is the only external arithmetic assertion needed for the asymptotic
version: the usual divisor-function estimate for positive natural numbers. -/
def NaturalDivisorEstimate (ε C : ℝ) : Prop :=
  ∀ n : ℕ, 0 < n → (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ ε

theorem count_quadruples_of_divisor_estimate (K L V : ℕ) (hL : 1 ≤ L) (hV : 1 ≤ V)
    (ε C : ℝ) (hε : 0 ≤ ε) (hC : 1 ≤ C) (hdiv : NaturalDivisorEstimate ε C)
    (S : Finset Quadruple) (hS : ∀ x ∈ S, Admissible K L V x) :
    (S.card : ℝ) ≤ 117 * K * (V : ℝ) ^ 2 * (L : ℝ) ^ 2 *
      (1 + 2 * C * (2 * (L : ℝ) * V) ^ ε) := by
  let B : ℝ := 2 * L * V
  let R : ℝ := 2 * C * B ^ ε
  let D : ℕ := Nat.ceil R
  have hB : 0 < B := by
    dsimp [B]
    have : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
    have : (0 : ℝ) < V := by exact_mod_cast (show 0 < V by omega)
    positivity
  have hR : 0 < R := by dsimp [R]; positivity
  have hDpos : 1 ≤ D := Nat.one_le_ceil_iff.mpr hR
  have hD : DivisorBound L V D := by
    intro n hn habs
    have hnabs : 0 < n.natAbs := Int.natAbs_pos.mpr hn
    have hh := hdiv n.natAbs hnabs
    have hni : (n.natAbs : ℤ) ≤ 2 * (L : ℤ) * V := by
      simpa only [Int.natCast_natAbs] using habs
    have hnr : (n.natAbs : ℝ) ≤ B := by dsimp [B]; exact_mod_cast hni
    have hpow := Real.rpow_le_rpow (Nat.cast_nonneg n.natAbs) hnr hε
    have hc : ((divisorsIn L n).card : ℝ) ≤ 2 * (n.natAbs.divisors.card : ℝ) := by
      exact_mod_cast card_divisorsIn_le L n hn
    have hbound : ((divisorsIn L n).card : ℝ) ≤ R := by
      dsimp [R]
      nlinarith
    exact_mod_cast hbound.trans (Nat.le_ceil R)
  have hcount : (S.card : ℝ) ≤ 117 * K * (V : ℝ) ^ 2 * (L : ℝ) ^ 2 * D := by
    exact_mod_cast count_quadruples K L V D hL hV hDpos S hS hD
  have hceil : (D : ℝ) ≤ 1 + R := by
    have := Nat.ceil_lt_add_one (le_of_lt hR)
    dsimp [D]
    linarith
  calc
    (S.card : ℝ) ≤ 117 * K * (V : ℝ) ^ 2 * (L : ℝ) ^ 2 * D := hcount
    _ ≤ 117 * K * (V : ℝ) ^ 2 * (L : ℝ) ^ 2 * (1 + R) := by gcongr
    _ = _ := by rfl

/-- The asymptotic shape of Lemma 3.2, with an explicit constant and only the
standard positive divisor estimate supplied as an external theorem parameter. -/
theorem lemma_3_2 (K L V A : ℕ) (hK : 1 ≤ K) (hL : 1 ≤ L) (hV : 1 ≤ V)
    (hA : 1 ≤ A) (hVK : V ≤ A * K) (ε C : ℝ) (hε : 0 ≤ ε) (hC : 1 ≤ C)
    (hdiv : NaturalDivisorEstimate ε C) :
    ((admissibleQuadruples K L V).card : ℝ) ≤
      (117 * (1 + 2 * C * (2 * (A : ℝ)) ^ ε)) *
        ((K : ℝ) * L) ^ ε * K * (V : ℝ) ^ 2 * (L : ℝ) ^ 2 := by
  have hmain := count_quadruples_of_divisor_estimate K L V hL hV ε C hε hC hdiv
    (admissibleQuadruples K L V) (fun _ hx => mem_admissibleQuadruples.mp hx)
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hVr : (V : ℝ) ≤ A * K := by exact_mod_cast hVK
  have hP : (1 : ℝ) ≤ (K : ℝ) * L := by nlinarith
  have hp : (1 : ℝ) ≤ ((K : ℝ) * L) ^ ε := Real.one_le_rpow hP hε
  have hbase : 2 * (L : ℝ) * V ≤ (2 * (A : ℝ)) * ((K : ℝ) * L) := by
    nlinarith
  have hpower : (2 * (L : ℝ) * V) ^ ε ≤
      (2 * (A : ℝ)) ^ ε * ((K : ℝ) * L) ^ ε := by
    rw [← Real.mul_rpow (by positivity : (0 : ℝ) ≤ 2 * A)
      (by positivity : (0 : ℝ) ≤ (K : ℝ) * L)]
    exact Real.rpow_le_rpow (by positivity) hbase hε
  have hbracket : 1 + 2 * C * (2 * (L : ℝ) * V) ^ ε ≤
      (1 + 2 * C * (2 * (A : ℝ)) ^ ε) * ((K : ℝ) * L) ^ ε := by
    nlinarith
  calc
    ((admissibleQuadruples K L V).card : ℝ) ≤
        117 * K * (V : ℝ) ^ 2 * (L : ℝ) ^ 2 *
          (1 + 2 * C * (2 * (L : ℝ) * V) ^ ε) := hmain
    _ ≤ 117 * K * (V : ℝ) ^ 2 * (L : ℝ) ^ 2 *
        ((1 + 2 * C * (2 * (A : ℝ)) ^ ε) * ((K : ℝ) * L) ^ ε) := by gcongr
    _ = _ := by ring

private def radialCode (x : Quadruple) : ℤ × ℤ × ℤ × ℤ :=
  (x.k4, x.l1, x.l2, x.l3)

/-- The all-equal-k family contributes at most K L³, with no divisor estimate. -/
theorem count_radial_quadruples (K L : ℕ) (S : Finset Quadruple)
    (hbox : ∀ x ∈ S, x ∈ allQuadruples K L)
    (he : ∀ x ∈ S, x.firstEquation)
    (hrad : ∀ x ∈ S, x.k1 = x.k4 ∧ x.k2 = x.k4 ∧ x.k3 = x.k4) :
    S.card ≤ K * L ^ 3 := by
  have hi : Set.InjOn radialCode (S : Set Quadruple) := by
    intro x hx y hy hcode
    have hxr := hrad x hx
    have hyr := hrad y hy
    have hxe := he x hx
    have hye := he y hy
    simp only [radialCode, Prod.mk.injEq] at hcode
    simp only [Quadruple.firstEquation] at hxe hye
    have hl4 : x.l4 = y.l4 := by omega
    cases x
    cases y
    simp_all
  have hm : Set.MapsTo radialCode (S : Set Quadruple)
      (↑(baseSet K ×ˢ radialSet L ×ˢ radialSet L ×ˢ radialSet L) :
        Set (ℤ × ℤ × ℤ × ℤ)) := by
    intro x hx
    have h := mem_allQuadruples.mp (hbox x hx)
    change radialCode x ∈ baseSet K ×ˢ radialSet L ×ˢ radialSet L ×ˢ radialSet L
    simp only [radialCode, mem_product]
    exact ⟨h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1⟩
  simpa [card_product, pow_succ, mul_assoc] using card_le_card_of_injOn radialCode hm hi

theorem count_including_radial (K L V D : ℕ) (hL : 1 ≤ L) (hV : 1 ≤ V)
    (hDpos : 1 ≤ D) (S : Finset Quadruple)
    (hbox : ∀ x ∈ S, x ∈ allQuadruples K L)
    (hfirst : ∀ x ∈ S, x.firstEquation) (hsecond : ∀ x ∈ S, x.secondEquation)
    (hdiff : ∀ x ∈ S, x.k1 - x.k4 ∈ differenceSet V ∧
      x.k2 - x.k4 ∈ differenceSet V ∧ x.k3 - x.k4 ∈ differenceSet V)
    (hD : DivisorBound L V D) :
    S.card ≤ 117 * K * V ^ 2 * L ^ 2 * D + K * L ^ 3 := by
  classical
  let radial : Quadruple → Prop := fun x =>
    x.k1 = x.k4 ∧ x.k2 = x.k4 ∧ x.k3 = x.k4
  let S₀ := S.filter radial
  let S₁ := S.filter (fun x => ¬ radial x)
  have hr : S₀.card ≤ K * L ^ 3 := count_radial_quadruples K L S₀
    (fun x hx => hbox x (mem_filter.mp hx).1)
    (fun x hx => hfirst x (mem_filter.mp hx).1)
    (fun _ hx => (mem_filter.mp hx).2)
  have ha : ∀ x ∈ S₁, Admissible K L V x := by
    intro x hx
    have hxS := (mem_filter.mp hx).1
    have hb := mem_allQuadruples.mp (hbox x hxS)
    have hd := hdiff x hxS
    exact ⟨hb.1, hb.2.1, hb.2.2.1, hb.2.2.2.1,
      hb.2.2.2.2.1, hb.2.2.2.2.2.1, hb.2.2.2.2.2.2.1, hb.2.2.2.2.2.2.2,
      hd.1, hd.2.1, hd.2.2, hfirst x hxS, hsecond x hxS, (mem_filter.mp hx).2⟩
  have hn := count_quadruples K L V D hL hV hDpos S₁ ha hD
  have hu : S ⊆ S₀ ∪ S₁ := by
    intro x hx
    by_cases h : radial x
    · exact mem_union_left _ (mem_filter.mpr ⟨hx, h⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨hx, h⟩)
  have hc := (card_le_card hu).trans (card_union_le S₀ S₁)
  omega

/-- Manuscript parameters may be real; this version records their actual
half-open integer intervals before rounding. -/
structure RealAdmissible (K L V : ℝ) (x : Quadruple) : Prop where
  k1_mem : (x.k1 : ℝ) ∈ Set.Ico K (2 * K)
  k2_mem : (x.k2 : ℝ) ∈ Set.Ico K (2 * K)
  k3_mem : (x.k3 : ℝ) ∈ Set.Ico K (2 * K)
  k4_mem : (x.k4 : ℝ) ∈ Set.Ico K (2 * K)
  l1_mem : (x.l1 : ℝ) ∈ Set.Ico L (2 * L)
  l2_mem : (x.l2 : ℝ) ∈ Set.Ico L (2 * L)
  l3_mem : (x.l3 : ℝ) ∈ Set.Ico L (2 * L)
  l4_mem : (x.l4 : ℝ) ∈ Set.Ico L (2 * L)
  d1_le : |((x.k1 - x.k4 : ℤ) : ℝ)| ≤ V
  d2_le : |((x.k2 - x.k4 : ℤ) : ℝ)| ≤ V
  d3_le : |((x.k3 - x.k4 : ℤ) : ℝ)| ≤ V
  first : x.firstEquation
  second : x.secondEquation
  nonradial : ¬ (x.k1 = x.k4 ∧ x.k2 = x.k4 ∧ x.k3 = x.k4)

private theorem real_interval_to_ceiling (X : ℝ) (hX : 1 ≤ X) (k : ℤ)
    (hk : (k : ℝ) ∈ Set.Ico X (2 * X)) : k ∈ baseSet (Nat.ceil X) := by
  simp only [baseSet, mem_Ico]
  constructor
  · rw [Int.natCast_ceil_eq_ceil (by linarith : 0 ≤ X)]
    exact Int.ceil_le.mpr hk.1
  · have hx := Nat.le_ceil X
    have hu : (k : ℝ) < 2 * (Nat.ceil X : ℝ) := by linarith [hk.2]
    exact_mod_cast hu

private theorem real_difference_to_ceiling (V : ℝ) (d : ℤ)
    (hd : |(d : ℝ)| ≤ V) : d ∈ differenceSet (Nat.ceil V) := by
  simp only [differenceSet, mem_Icc]
  apply abs_le.mp
  have h : |(d : ℝ)| ≤ (Nat.ceil V : ℝ) := hd.trans (Nat.le_ceil V)
  exact_mod_cast h

theorem RealAdmissible.ceiling {K L V : ℝ} {x : Quadruple}
    (h : RealAdmissible K L V x) (hK : 1 ≤ K) (hL : 1 ≤ L) :
    Admissible (Nat.ceil K) (Nat.ceil L) (Nat.ceil V) x := by
  exact ⟨real_interval_to_ceiling K hK x.k1 h.k1_mem,
    real_interval_to_ceiling K hK x.k2 h.k2_mem,
    real_interval_to_ceiling K hK x.k3 h.k3_mem,
    real_interval_to_ceiling K hK x.k4 h.k4_mem,
    real_interval_to_ceiling L hL x.l1 h.l1_mem,
    real_interval_to_ceiling L hL x.l2 h.l2_mem,
    real_interval_to_ceiling L hL x.l3 h.l3_mem,
    real_interval_to_ceiling L hL x.l4 h.l4_mem,
    real_difference_to_ceiling V _ h.d1_le,
    real_difference_to_ceiling V _ h.d2_le,
    real_difference_to_ceiling V _ h.d3_le, h.first, h.second, h.nonradial⟩

private theorem ceil_le_twice (X : ℝ) (hX : 1 ≤ X) : (Nat.ceil X : ℝ) ≤ 2 * X := by
  have := Nat.ceil_lt_add_one (by linarith : 0 ≤ X)
  linarith

theorem count_real_parameters (K L V : ℝ) (hK : 1 ≤ K) (hL : 1 ≤ L) (hV : 1 ≤ V)
    (ε C : ℝ) (hε : 0 ≤ ε) (hC : 1 ≤ C) (hdiv : NaturalDivisorEstimate ε C)
    (S : Finset Quadruple) (hS : ∀ x ∈ S, RealAdmissible K L V x) :
    (S.card : ℝ) ≤ 3744 * K * V ^ 2 * L ^ 2 * (1 + 2 * C * (8 * L * V) ^ ε) := by
  have hLc : 1 ≤ Nat.ceil L := Nat.one_le_ceil_iff.mpr (by linarith)
  have hVc : 1 ≤ Nat.ceil V := Nat.one_le_ceil_iff.mpr (by linarith)
  have hc := count_quadruples_of_divisor_estimate (Nat.ceil K) (Nat.ceil L)
    (Nat.ceil V) hLc hVc ε C hε hC hdiv S (fun x hx => (hS x hx).ceiling hK hL)
  have hk := ceil_le_twice K hK
  have hl := ceil_le_twice L hL
  have hv := ceil_le_twice V hV
  have hb : 2 * (Nat.ceil L : ℝ) * Nat.ceil V ≤ 8 * L * V := by
    calc
      _ ≤ 2 * (2 * L) * (2 * V) := by gcongr
      _ = _ := by ring
  have hp := Real.rpow_le_rpow (by positivity) hb hε
  calc
    (S.card : ℝ) ≤ 117 * (Nat.ceil K : ℝ) * (Nat.ceil V : ℝ) ^ 2 *
        (Nat.ceil L : ℝ) ^ 2 * (1 + 2 * C * (2 * (Nat.ceil L : ℝ) * Nat.ceil V) ^ ε) := hc
    _ ≤ 117 * (2 * K) * (2 * V) ^ 2 * (2 * L) ^ 2 *
        (1 + 2 * C * (8 * L * V) ^ ε) := by gcongr
    _ = _ := by ring

/-- Real-parameter version of Lemma 3.2, including the ceiling bridge. -/
theorem lemma_3_2_real (K L V A : ℝ) (hK : 1 ≤ K) (hL : 1 ≤ L) (hV : 1 ≤ V)
    (hA : 1 ≤ A) (hVK : V ≤ A * K) (ε C : ℝ) (hε : 0 ≤ ε) (hC : 1 ≤ C)
    (hdiv : NaturalDivisorEstimate ε C) (S : Finset Quadruple)
    (hS : ∀ x ∈ S, RealAdmissible K L V x) :
    (S.card : ℝ) ≤ (3744 * (1 + 2 * C * (8 * A) ^ ε)) *
      (K * L) ^ ε * K * V ^ 2 * L ^ 2 := by
  have hmain := count_real_parameters K L V hK hL hV ε C hε hC hdiv S hS
  have hP : 1 ≤ K * L := by nlinarith
  have hp : 1 ≤ (K * L) ^ ε := Real.one_le_rpow hP hε
  have hbase : 8 * L * V ≤ (8 * A) * (K * L) := by nlinarith
  have hpower : (8 * L * V) ^ ε ≤ (8 * A) ^ ε * (K * L) ^ ε := by
    rw [← Real.mul_rpow (by positivity : 0 ≤ 8 * A) (by positivity : 0 ≤ K * L)]
    exact Real.rpow_le_rpow (by positivity) hbase hε
  have hbracket : 1 + 2 * C * (8 * L * V) ^ ε ≤
      (1 + 2 * C * (8 * A) ^ ε) * (K * L) ^ ε := by nlinarith
  calc
    (S.card : ℝ) ≤ 3744 * K * V ^ 2 * L ^ 2 * (1 + 2 * C * (8 * L * V) ^ ε) := hmain
    _ ≤ 3744 * K * V ^ 2 * L ^ 2 * ((1 + 2 * C * (8 * A) ^ ε) * (K * L) ^ ε) := by
      gcongr
    _ = _ := by ring

/-- Quantifier order matching the manuscript's `≪ε` notation. The displayed
external hypothesis is definitionally the proposition named
`ClassicalInputs.DivisorBound` in the main development. -/
theorem lemma_3_2_uniform
    (hdiv : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ ε)
    (A : ℝ) (hA : 1 ≤ A) :
    ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 < B ∧
      ∀ K L V : ℝ, 1 ≤ K → 1 ≤ L → 1 ≤ V → V ≤ A * K →
        ∀ S : Finset Quadruple, (∀ x ∈ S, RealAdmissible K L V x) →
          (S.card : ℝ) ≤ B * (K * L) ^ ε * K * V ^ 2 * L ^ 2 := by
  intro ε hε
  obtain ⟨C, hC, hτ⟩ := hdiv ε hε
  have hC1 : 1 ≤ C := by simpa using hτ 1 (by omega)
  refine ⟨3744 * (1 + 2 * C * (8 * A) ^ ε), by positivity, ?_⟩
  intro K L V hK hL hV hVK S hS
  apply lemma_3_2_real K L V A hK hL hV hA hVK ε C hε.le hC1 _ S hS
  intro n hn
  exact hτ n (by omega)

end
end CircleDivisor.SpacingCount
