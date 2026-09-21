import CircleDivisor.EnergyV3.EnvelopeEnergies
import CircleDivisor.EnergyV3.QuadraticDecomposition
import CircleDivisor.EnergyV3.NeighborCount

/-! Actual quadratic orthogonality for the common band-limited localizer.
The first envelope mass is proved from this identity and the overlap bound;
it is not an analytic input. -/

namespace CircleDivisor.EnergyV3.FirstMass
noncomputable section
open MeasureTheory FourierLocalization FourierEnergy PairEnergies
open scoped BigOperators FourierTransform ComplexConjugate

abbrev Space := FourierLocalization.Space

theorem schwartzSecond_coe (χ : SchwartzMap Space ℂ) :
    (schwartzMul χ (schwartzConj χ) : Space → ℂ) = secondWeight χ := by
  funext x
  simp [secondWeight, Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem integrable_secondWeight (χ : SchwartzMap Space ℂ) : Integrable (secondWeight χ) := by
  rw [← schwartzSecond_coe]
  exact (schwartzMul χ (schwartzConj χ)).integrable

theorem support_secondWeight (χ : SchwartzMap Space ℂ) (c : ℝ)
    (hχ : Function.support (𝓕 (χ : Space → ℂ)) ⊆ Metric.ball 0 c) :
    Function.support (𝓕 (secondWeight χ)) ⊆ Metric.ball 0 (2 * c) := by
  simpa only [schwartzSecond_coe, ← two_mul] using
    support_fourier_schwartzMul χ (schwartzConj χ) c c hχ
      (support_fourier_schwartzConj χ c hχ)

theorem secondWeight_dilate (P : ℝ) (χ : Space → ℂ) :
    secondWeight (dilate P χ) = dilate P (secondWeight χ) := rfl

theorem integral_secondWeight_dilate (P : ℝ) (hP : 0 ≤ P) (χ : Space → ℂ) :
    (∫ x, ‖dilate P χ x‖ ^ 2) = P ^ 3 * ∫ x, ‖χ x‖ ^ 2 := by
  simpa [dilate] using Measure.integral_comp_inv_smul_of_nonneg volume
    (fun x => ‖χ x‖ ^ 2) hP

def atoms (K L : ℝ) (χ : SchwartzMap Space ℂ) (a : Point → ℂ) : Point → Space → ℂ :=
  weightedAtoms a (localizedAtoms (dilate (K * L) χ) (fun p : Point => coneFrequency K L p.1 p.2))

theorem pair_integrable (K L : ℝ) (hKL : 0 < K * L)
    (χ : SchwartzMap Space ℂ) (a : Point → ℂ) (p r : Point) :
    Integrable (pairValue (atoms K L χ a) (p, r)) := by
  have hi := integrable_weighted_character
    ((integrable_secondWeight χ).comp_smul (inv_ne_zero hKL.ne'))
    (coneFrequency K L p.1 p.2 - coneFrequency K L r.1 r.2)
  have heq : pairValue (atoms K L χ a) (p, r) = fun x =>
      (a p * conj (a r)) * (secondWeight (dilate (K * L) χ) x *
        character (coneFrequency K L p.1 p.2 - coneFrequency K L r.1 r.2) x) := by
    funext x
    rw [show pairValue (atoms K L χ a) (p, r) x =
      (a p * conj (a r)) * pairValue
        (localizedAtoms (dilate (K * L) χ) (fun p : Point => coneFrequency K L p.1 p.2)) (p,r) x by
          simp [atoms, weightedAtoms, pairValue]; ring]
    rw [localized_pairValue]
  rw [heq]
  exact hi.const_mul _

theorem off_diagonal_integral (K L c : ℝ) (hK : 1 ≤ K) (hL : 0 < L) (hc : 2 * c ≤ 1)
    (χ : SchwartzMap Space ℂ)
    (hχ : Function.support (𝓕 (χ : Space → ℂ)) ⊆ Metric.ball 0 c)
    (p r : Point) (hp : p.2 ≠ 0) (hne : p ≠ r) :
    (∫ x, pairValue
      (localizedAtoms (dilate (K * L) χ) (fun p : Point => coneFrequency K L p.1 p.2)) (p,r) x) = 0 := by
  rw [integral_localized_pairValue]
  by_contra hn
  have hKL : 0 < K * L := mul_pos (by linarith) hL
  have hs := support_fourier_dilate (K * L) hKL (secondWeight χ) (2 * c)
    (support_secondWeight χ c hχ) hn
  have hsmall : ‖coneFrequency K L r.1 r.2 - coneFrequency K L p.1 p.2‖ < 1 / (K * L) := by
    have hs' : ‖coneFrequency K L r.1 r.2 - coneFrequency K L p.1 p.2‖ < 2 * c / (K * L) := by
      simpa only [← secondWeight_dilate, Metric.mem_ball, dist_zero_right] using hs
    exact hs'.trans_le (div_le_div_of_nonneg_right hc hKL.le)
  have hb := small_difference_forces_balance K L hK hL Prod.fst Prod.snd (p,r) (r,r) (by
    simpa only [differenceFrequency, sub_self, sub_zero, norm_sub_rev] using hsmall)
  apply hne
  have hl : p.2 = r.2 := by dsimp [frequencyBalance] at hb; omega
  have hk : p.1 * p.2 = r.1 * p.2 := by dsimp [frequencyBalance] at hb; rw [← hl] at hb; omega
  exact Prod.ext (mul_right_cancel₀ hp hk) hl

theorem pair_integral (K L c : ℝ) (hK : 1 ≤ K) (hL : 0 < L) (hc : 2 * c ≤ 1)
    (χ : SchwartzMap Space ℂ)
    (hχ : Function.support (𝓕 (χ : Space → ℂ)) ⊆ Metric.ball 0 c)
    (a : Point → ℂ) (p r : Point) (hp : p.2 ≠ 0) :
    (∫ x, pairValue (atoms K L χ a) (p,r) x) =
      if p = r then (((K * L) ^ 3 * (∫ x, ‖χ x‖ ^ 2) * ‖a p‖ ^ 2 : ℝ) : ℂ) else 0 := by
  classical
  have hw : pairValue (atoms K L χ a) (p,r) = fun x =>
      (a p * conj (a r)) * pairValue
        (localizedAtoms (dilate (K * L) χ) (fun p : Point => coneFrequency K L p.1 p.2)) (p,r) x := by
    funext x
    simp [atoms, weightedAtoms, pairValue]
    ring
  rw [hw, integral_const_mul]
  by_cases he : p = r
  · subst r
    rw [if_pos rfl]
    have hv : pairValue (localizedAtoms (dilate (K * L) χ)
        (fun p : Point => coneFrequency K L p.1 p.2)) (p,p) =
          fun x => ((‖dilate (K * L) χ x‖ ^ 2 : ℝ) : ℂ) := by
      funext x
      simp [localized_pairValue, character, secondWeight]
    rw [hv]
    dsimp only
    rw [integral_complex_ofReal, integral_secondWeight_dilate (K * L) (by positivity),
      Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  · rw [if_neg he, off_diagonal_integral K L c hK hL hc χ hχ p r hp he, mul_zero]

theorem square_expansion {ι : Type*} (S : Finset ι) (f : ι → Space → ℂ) (x : Space) :
    ‖∑ p ∈ S, f p x‖ ^ 2 = ∑ p ∈ S, ∑ r ∈ S, (pairValue f (p,r) x).re := by
  have hh := congrArg Complex.re (pairSum_all_pairs S f x)
  rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq] at hh
  simpa only [pairSum, Finset.sum_product, Complex.re_sum] using hh.symm

theorem sum_square_integrable (K L : ℝ) (hKL : 0 < K * L)
    (χ : SchwartzMap Space ℂ) (a : Point → ℂ) (S : Finset Point) :
    Integrable (fun x => ‖∑ p ∈ S, atoms K L χ a p x‖ ^ 2) := by
  simp_rw [square_expansion]
  exact integrable_finsetSum S (fun p hp =>
    integrable_finsetSum S (fun r hr => (pair_integrable K L hKL χ a p r).re))

/-- Exact L² diagonal orthogonality for the actual localized weighted atoms. -/
theorem sum_square_integral (K L c : ℝ) (hK : 1 ≤ K) (hL : 0 < L) (hc : 2 * c ≤ 1)
    (χ : SchwartzMap Space ℂ)
    (hχ : Function.support (𝓕 (χ : Space → ℂ)) ⊆ Metric.ball 0 c)
    (a : Point → ℂ) (S : Finset Point) (hS : ∀ p ∈ S, p.2 ≠ 0) :
    (∫ x, ‖∑ p ∈ S, atoms K L χ a p x‖ ^ 2) =
      (K * L) ^ 3 * (∫ x, ‖χ x‖ ^ 2) * ∑ p ∈ S, ‖a p‖ ^ 2 := by
  classical
  have hKL : 0 < K * L := mul_pos (by linarith) hL
  simp_rw [square_expansion]
  rw [integral_finsetSum S, Finset.mul_sum]
  · apply Finset.sum_congr rfl
    intro p hp
    rw [integral_finsetSum S]
    · have hi (r : Point) : (∫ x, (pairValue (atoms K L χ a) (p,r) x).re) =
          (∫ x, pairValue (atoms K L χ a) (p,r) x).re :=
        integral_re (pair_integrable K L hKL χ a p r)
      simp_rw [hi, pair_integral K L c hK hL hc χ hχ a p _ (hS p hp)]
      simp_rw [apply_ite Complex.re]
      simp [hp, ← Complex.ofReal_mul, ← Complex.ofReal_pow]
    · intro r hr
      exact (pair_integrable K L hKL χ a p r).re
  · intro p hp
    exact integrable_finsetSum S (fun r _ => (pair_integrable K L hKL χ a p r).re)

theorem sum_square_integral_le (K L c : ℝ) (hK : 1 ≤ K) (hL : 0 < L) (hc : 2 * c ≤ 1)
    (χ : SchwartzMap Space ℂ)
    (hχ : Function.support (𝓕 (χ : Space → ℂ)) ⊆ Metric.ball 0 c)
    (a : Point → ℂ) (S : Finset Point) (hS : ∀ p ∈ S, p.2 ≠ 0)
    (ha : ∀ p ∈ S, ‖a p‖ ≤ 1) :
    (∫ x, ‖∑ p ∈ S, atoms K L χ a p x‖ ^ 2) ≤
      (K * L) ^ 3 * (∫ x, ‖χ x‖ ^ 2) * (S.card : ℝ) := by
  rw [sum_square_integral K L c hK hL hc χ hχ a S hS]
  apply mul_le_mul_of_nonneg_left
  · calc
      _ ≤ ∑ _p ∈ S, (1 : ℝ) := Finset.sum_le_sum (fun p hp => by
        nlinarith [ha p hp, norm_nonneg (a p)])
      _ = _ := by simp
  · positivity

theorem family_square_integral_le {ι : Type*} (T : Finset ι) (S : ι → Finset Point)
    (K L c : ℝ) (hK : 1 ≤ K) (hL : 0 < L) (hc : 2 * c ≤ 1)
    (χ : SchwartzMap Space ℂ)
    (hχ : Function.support (𝓕 (χ : Space → ℂ)) ⊆ Metric.ball 0 c)
    (a : Point → ℂ) (hS : ∀ i ∈ T, ∀ p ∈ S i, p.2 ≠ 0)
    (ha : ∀ i ∈ T, ∀ p ∈ S i, ‖a p‖ ≤ 1) :
    (∑ i ∈ T, ∫ x, ‖∑ p ∈ S i, atoms K L χ a p x‖ ^ 2) ≤
      (K * L) ^ 3 * (∫ x, ‖χ x‖ ^ 2) * ∑ i ∈ T, ((S i).card : ℝ) := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun i hi => sum_square_integral_le K L c hK hL hc χ hχ a (S i) (hS i hi) (ha i hi))

theorem disjoint_family_card {ι : Type*} (T : Finset ι) (S : ι → Finset Point)
    (hdisj : (T : Set ι).PairwiseDisjoint S) (U : Finset Point)
    (hSU : ∀ i ∈ T, S i ⊆ U) : (∑ i ∈ T, ((S i).card : ℝ)) ≤ U.card := by
  classical
  have hh : T.biUnion S ⊆ U := by
    intro p hp
    obtain ⟨i, hi, hpi⟩ := Finset.mem_biUnion.mp hp
    exact hSU i hi hpi
  have hc := Finset.card_le_card hh
  rw [Finset.card_biUnion hdisj] at hc
  exact_mod_cast hc

def groupedSquare {β : Type*} [DecidableEq β] (S : Finset Point) (c : Point → β)
    (f : Point → Space → ℂ) (x : Space) : ℝ :=
  ∑ b ∈ S.image c, ‖∑ p ∈ S.filter (fun p => c p = b), f p x‖ ^ 2

theorem groupedSquare_nonneg {β : Type*} [DecidableEq β] (S : Finset Point)
    (c : Point → β) (f : Point → Space → ℂ) (x : Space) : 0 ≤ groupedSquare S c f x := by
  unfold groupedSquare
  positivity

theorem groupedSquare_pairSum {β : Type*} [DecidableEq β] (S : Finset Point)
    (c : Point → β) (f : Point → Space → ℂ) (x : Space) :
    groupedSquare S c f x =
      (pairSum ((S ×ˢ S).filter (fun p => c p.1 = c p.2)) f x).re := by
  rw [QuadraticDecomposition.grouped_pairSum]
  simp only [groupedSquare, Complex.re_sum, Complex.ofReal_re]

theorem groupedSquare_integrable {β : Type*} [DecidableEq β]
    (K L : ℝ) (hKL : 0 < K * L) (χ : SchwartzMap Space ℂ) (a : Point → ℂ)
    (S : Finset Point) (c : Point → β) :
    Integrable (groupedSquare S c (atoms K L χ a)) :=
  integrable_finsetSum _ (fun _ _ => sum_square_integrable K L hKL χ a _)

theorem fiber_disjoint {β : Type*} [DecidableEq β] (S : Finset Point) (c : Point → β) :
    (S.image c : Set β).PairwiseDisjoint (fun b => S.filter (fun p => c p = b)) := by
  intro b hb d hd hbd
  apply Finset.disjoint_left.mpr
  intro p hp hq
  exact hbd ((Finset.mem_filter.mp hp).2.symm.trans (Finset.mem_filter.mp hq).2)

theorem groupedSquare_integral_le {β : Type*} [DecidableEq β]
    (K L c : ℝ) (hK : 1 ≤ K) (hL : 0 < L) (hc : 2 * c ≤ 1)
    (χ : SchwartzMap Space ℂ)
    (hχ : Function.support (𝓕 (χ : Space → ℂ)) ⊆ Metric.ball 0 c)
    (a : Point → ℂ) (S : Finset Point) (classify : Point → β)
    (hS : ∀ p ∈ S, p.2 ≠ 0) (ha : ∀ p ∈ S, ‖a p‖ ≤ 1) :
    (∫ x, groupedSquare S classify (atoms K L χ a) x) ≤
      (K * L) ^ 3 * (∫ x, ‖χ x‖ ^ 2) * (S.card : ℝ) := by
  have hKL : 0 < K * L := mul_pos (by linarith) hL
  unfold groupedSquare
  rw [integral_finsetSum _ (fun b _ => sum_square_integrable K L hKL χ a _)]
  apply (family_square_integral_le (S.image classify) (fun b => S.filter (fun p => classify p=b))
    K L c hK hL hc χ hχ a (fun b hb p hp => hS p (Finset.mem_filter.mp hp).1)
    (fun b hb p hp => ha p (Finset.mem_filter.mp hp).1)).trans
  apply mul_le_mul_of_nonneg_left
    (disjoint_family_card (S.image classify) _ (fiber_disjoint S classify) S
      (fun b hb => Finset.filter_subset _ _))
  positivity

theorem dyadic_point_card (S : Finset Point) (K L : ℝ) (hK : 1 ≤ K) (hL : 1 ≤ L)
    (hS : ∀ p ∈ S, K ≤ (p.1 : ℝ) ∧ (p.1 : ℝ) < 2*K ∧
      L ≤ (p.2 : ℝ) ∧ (p.2 : ℝ) < 2*L) : (S.card : ℝ) ≤ 36 * (K * L) := by
  rcases S.eq_empty_or_nonempty with he | ⟨center, hcenter⟩
  · simp [he]
    positivity
  · have hh := NeighborCount.integer_neighbor_count S center (A := L) (B := K)
      (by linarith) (by linarith) (by
        intro p hp
        have hc := hS center hcenter
        have hp := hS p hp
        push_cast
        constructor <;> rw [abs_le] <;> constructor <;> linarith)
    have hmul := mul_le_mul (show 1+L ≤ 2*L by linarith) (show 1+K ≤ 2*K by linarith)
      (by linarith : 0 ≤ 1+K) (by linarith : 0 ≤ 2*L)
    nlinarith

/-- The actual infinite envelope lattice, after an arbitrary fixed physical
linear change of coordinates. Classification may be by fine cap or by ray. -/
theorem envelope_grouped_first_mass {β : Type*} [DecidableEq β]
    (n j : ℕ) (S : GuthMaldague.CapIndex j → Finset Point) (U : Finset Point)
    (hdisj : ((Finset.univ : Finset (GuthMaldague.CapIndex j)) : Set (GuthMaldague.CapIndex j)).PairwiseDisjoint S)
    (hSU : ∀ i, S i ⊆ U) (classify : Point → β) (e : Space ≃L[ℝ] Space)
    (K L c : ℝ) (hK : 1 ≤ K) (hL : 1 ≤ L) (hc : 2 * c ≤ 1)
    (hU : ∀ p ∈ U, K ≤ (p.1 : ℝ) ∧ (p.1 : ℝ) < 2*K ∧
      L ≤ (p.2 : ℝ) ∧ (p.2 : ℝ) < 2*L)
    (χ : SchwartzMap Space ℂ)
    (hχ : Function.support (𝓕 (χ : Space → ℂ)) ⊆ Metric.ball 0 c)
    (a : Point → ℂ) (ha : ∀ p ∈ U, ‖a p‖ ≤ 1) :
    (∀ i : GuthMaldague.CapIndex j, Summable (fun m : GuthMaldague.Lattice =>
      ∫ x, groupedSquare (S i) classify (atoms K L χ a) (e x) * GuthMaldague.envelopeWeight n j i m x)) ∧
    (∑ i : GuthMaldague.CapIndex j, ∑' m : GuthMaldague.Lattice,
      ∫ x, groupedSquare (S i) classify (atoms K L χ a) (e x) * GuthMaldague.envelopeWeight n j i m x) ≤
        36 * EnvelopeEnergies.overlapBound * LinearTransport.jacobian e *
          (∫ x, ‖χ x‖ ^ 2) * (K * L) ^ 3 * (K * L) := by
  classical
  have hL0 : 0 < L := by linarith
  have hKL : 0 < K * L := mul_pos (by linarith) hL0
  have hnn (p : Point) (hp : p ∈ U) : p.2 ≠ 0 := by
    have hh := (hU p hp).2.2.1
    intro hz
    simp only [hz, Int.cast_zero] at hh
    linarith
  have hi (i : GuthMaldague.CapIndex j) :=
    (LinearTransport.integrable_comp_iff e _).mpr
      (groupedSquare_integrable K L hKL χ a (S i) classify)
  have hw (i : GuthMaldague.CapIndex j) := EnvelopeEnergies.countable_first_mass n j i
    (fun x => groupedSquare (S i) classify (atoms K L χ a) (e x)) (hi i)
      (fun x => groupedSquare_nonneg _ _ _ _)
  refine ⟨fun i => (hw i).1, ?_⟩
  have hsum : (∑ i : GuthMaldague.CapIndex j, ∫ x, groupedSquare (S i) classify (atoms K L χ a) x) ≤
      (K * L) ^ 3 * (∫ x, ‖χ x‖ ^ 2) * (U.card : ℝ) := by
    calc
      _ ≤ ∑ i : GuthMaldague.CapIndex j,
          (K * L) ^ 3 * (∫ x, ‖χ x‖ ^ 2) * ((S i).card : ℝ) :=
        Finset.sum_le_sum (fun i _ => groupedSquare_integral_le K L c hK hL0 hc χ hχ a (S i) classify
          (fun p hp => hnn p (hSU i hp)) (fun p hp => ha p (hSU i hp)))
      _ = (K * L) ^ 3 * (∫ x, ‖χ x‖ ^ 2) * ∑ i : GuthMaldague.CapIndex j, ((S i).card : ℝ) :=
        (Finset.mul_sum ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (disjoint_family_card Finset.univ S hdisj U (fun i _ => hSU i)) (by positivity)
  have hcov := EnvelopeEnergies.overlapBound_nonneg
  have hjac := (LinearTransport.jacobian_pos e).le
  calc
    _ ≤ ∑ i : GuthMaldague.CapIndex j,
        EnvelopeEnergies.overlapBound * ∫ x, groupedSquare (S i) classify (atoms K L χ a) (e x) :=
      Finset.sum_le_sum (fun i _ => (hw i).2)
    _ = (EnvelopeEnergies.overlapBound * LinearTransport.jacobian e) *
        ∑ i : GuthMaldague.CapIndex j, ∫ x, groupedSquare (S i) classify (atoms K L χ a) x := by
      simp_rw [LinearTransport.integral_comp, ← mul_assoc]
      rw [Finset.mul_sum]
    _ ≤ (EnvelopeEnergies.overlapBound * LinearTransport.jacobian e) *
        ((K * L) ^ 3 * (∫ x, ‖χ x‖ ^ 2) * (U.card : ℝ)) :=
      mul_le_mul_of_nonneg_left hsum (mul_nonneg hcov hjac)
    _ ≤ (EnvelopeEnergies.overlapBound * LinearTransport.jacobian e) *
        ((K * L) ^ 3 * (∫ x, ‖χ x‖ ^ 2) * (36 * (K * L))) := by
      gcongr
      exact dyadic_point_card U K L hK hL hU
    _ = _ := by ring

/-- Once the actual sharp projections are identified with the finite atom
groups, the GM local masses inherit the proved first-mass bound. The only
extra premise is that pointwise identification, not a mass estimate. -/
theorem localMass_first_mass {β : Type*} [DecidableEq β]
    (n j : ℕ) (S : GuthMaldague.CapIndex j → Finset Point) (U : Finset Point)
    (hdisj : ((Finset.univ : Finset (GuthMaldague.CapIndex j)) : Set (GuthMaldague.CapIndex j)).PairwiseDisjoint S)
    (hSU : ∀ i, S i ⊆ U) (classify : Point → β) (e : Space ≃L[ℝ] Space)
    (K L c : ℝ) (hK : 1 ≤ K) (hL : 1 ≤ L) (hc : 2 * c ≤ 1)
    (hU : ∀ p ∈ U, K ≤ (p.1 : ℝ) ∧ (p.1 : ℝ) < 2*K ∧
      L ≤ (p.2 : ℝ) ∧ (p.2 : ℝ) < 2*L)
    (χ : SchwartzMap Space ℂ)
    (hχ : Function.support (𝓕 (χ : Space → ℂ)) ⊆ Metric.ball 0 c)
    (a : Point → ℂ) (ha : ∀ p ∈ U, ‖a p‖ ≤ 1) (f : Space → ℂ)
    (hpartial : ∀ i x, GuthMaldague.partialSquare n j i f x =
      groupedSquare (S i) classify (atoms K L χ a) (e x)) :
    (∀ i : GuthMaldague.CapIndex j, Summable (fun m : GuthMaldague.Lattice =>
      GuthMaldague.envelopeVolume n j i m * GuthMaldague.localMass n j i m f)) ∧
    (∑ i : GuthMaldague.CapIndex j, ∑' m : GuthMaldague.Lattice,
      GuthMaldague.envelopeVolume n j i m * GuthMaldague.localMass n j i m f) ≤
        36 * EnvelopeEnergies.overlapBound * LinearTransport.jacobian e *
          (∫ x, ‖χ x‖ ^ 2) * (K * L) ^ 3 * (K * L) := by
  have hterm (i : GuthMaldague.CapIndex j) (m : GuthMaldague.Lattice) :
      GuthMaldague.envelopeVolume n j i m * GuthMaldague.localMass n j i m f =
        ∫ x, groupedSquare (S i) classify (atoms K L χ a) (e x) * GuthMaldague.envelopeWeight n j i m x := by
    unfold GuthMaldague.localMass
    rw [mul_div_cancel₀ _ (WeightMass.envelopeVolume_pos n j i m).ne']
    simp_rw [hpartial]
  simp_rw [hterm]
  exact envelope_grouped_first_mass n j S U hdisj hSU classify e K L c hK hL hc hU χ hχ a ha

theorem envelope_average_ofReal (n j : ℕ) (i : GuthMaldague.CapIndex j)
    (m : GuthMaldague.Lattice) (g : Space → ℝ) :
    EnvelopeEnergies.envelopePairAverage n j i (fun x => (g x : ℂ)) m =
      (((∫ x, g x * GuthMaldague.envelopeWeight n j i m x) /
        GuthMaldague.envelopeVolume n j i m : ℝ) : ℂ) := by
  unfold EnvelopeEnergies.envelopePairAverage CountableAveraging.average
  simp_rw [← Complex.ofReal_mul]
  rw [integral_complex_ofReal]
  push_cast
  rw [div_eq_mul_inv, mul_comm]
  congr 1
  congr 1
  apply integral_congr_ae
  filter_upwards with x
  ring

theorem envelope_grouped_average {β : Type*} [DecidableEq β]
    (n j : ℕ) (i : GuthMaldague.CapIndex j) (m : GuthMaldague.Lattice)
    (S : Finset Point) (classify : Point → β) (f : Point → Space → ℂ) (e : Space → Space) :
    EnvelopeEnergies.envelopePairAverage n j i
      (fun x => pairSum ((S ×ˢ S).filter (fun p => classify p.1 = classify p.2)) f (e x)) m =
        (((∫ x, groupedSquare S classify f (e x) * GuthMaldague.envelopeWeight n j i m x) /
          GuthMaldague.envelopeVolume n j i m : ℝ) : ℂ) := by
  have hh : (fun x => pairSum ((S ×ˢ S).filter (fun p => classify p.1 = classify p.2)) f (e x)) =
      fun x => (groupedSquare S classify f (e x) : ℂ) := by
    funext x
    rw [QuadraticDecomposition.grouped_pairSum]
    simp only [groupedSquare, Complex.ofReal_sum]
  rw [hh]
  exact envelope_average_ofReal n j i m _

theorem envelope_grouped_average_nonneg {β : Type*} [DecidableEq β]
    (n j : ℕ) (i : GuthMaldague.CapIndex j) (m : GuthMaldague.Lattice)
    (S : Finset Point) (classify : Point → β) (f : Point → Space → ℂ) (e : Space → Space) :
    0 ≤ (∫ x, groupedSquare S classify f (e x) * GuthMaldague.envelopeWeight n j i m x) /
      GuthMaldague.envelopeVolume n j i m :=
  div_nonneg (integral_nonneg (fun x => mul_nonneg (groupedSquare_nonneg _ _ _ _)
    (GuthMaldague.envelopeWeight_nonneg n j i m x))) (WeightMass.envelopeVolume_pos n j i m).le

end
end CircleDivisor.EnergyV3.FirstMass
