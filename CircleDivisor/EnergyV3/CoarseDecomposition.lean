import CircleDivisor.EnergyV3.FirstMass
import CircleDivisor.EnergyV3.CapNesting

/-! The actual coarse-cap point sets and quadratic decomposition. The cap
functions below are the sharp Fourier projections in the external interface. -/
namespace CircleDivisor.EnergyV3.CoarseDecomposition
noncomputable section
open MeasureTheory GuthMaldague FourierEnergy
open scoped BigOperators
abbrev Point := ℤ × ℤ
abbrev Pair := Point × Point
abbrev Space := GuthMaldague.Space

def coarsePoints (n j : ℕ) (I : Finset Point) (θ : ℤ → CapIndex n) (i : CapIndex j) : Finset Point :=
  I.filter (fun p => θ p.1 ∈ fineChildren n j i)

def fullPairs (n : ℕ) (S : Finset Point) (θ : ℤ → CapIndex n) : Finset Pair :=
  (S ×ˢ S).filter (fun p => θ p.1.1 = θ p.2.1)

def samePairs (S : Finset Point) : Finset Pair :=
  (S ×ˢ S).filter (fun p => p.1.1 = p.2.1)

def crossPairs (n : ℕ) (S : Finset Point) (θ : ℤ → CapIndex n) : Finset Pair :=
  (fullPairs n S θ).filter (fun p => p.1.1 ≠ p.2.1)

theorem coarsePoints_subset (n j : ℕ) (I : Finset Point) (θ : ℤ → CapIndex n) (i : CapIndex j) :
    coarsePoints n j I θ i ⊆ I := Finset.filter_subset _ _

theorem coarsePoints_pairwiseDisjoint (n j : ℕ) (I : Finset Point) (θ : ℤ → CapIndex n)
    (hθ : ∀ p∈I, (cap n (θ p.1)).Nonempty) :
    (Set.univ : Set (CapIndex j)).PairwiseDisjoint (coarsePoints n j I θ) := by
  intro i hi i' hi' hne
  exact CapNesting.coarsePoints_disjoint I n j (fun p => θ p.1) hθ hne

theorem pairRelations_disjoint {β : Type*} (S : β→Finset Point) (F : β→Finset Pair)
    (hS : (Set.univ : Set β).PairwiseDisjoint S) (hF : ∀ i, F i⊆S i×ˢ S i) :
    (Set.univ : Set β).PairwiseDisjoint F := by
  intro i hi k hk hik
  apply Finset.disjoint_left.mpr
  intro p hp hq
  exact Finset.disjoint_left.mp (hS hi hk hik)
    (Finset.mem_product.mp (hF i hp)).1 (Finset.mem_product.mp (hF k hq)).1

theorem samePairs_subset (S : Finset Point) : samePairs S⊆S×ˢ S := Finset.filter_subset _ _

theorem fullPairs_subset (n : ℕ) (S : Finset Point) (θ : ℤ→CapIndex n) :
    fullPairs n S θ⊆S×ˢ S := Finset.filter_subset _ _

theorem crossPairs_subset (n : ℕ) (S : Finset Point) (θ : ℤ→CapIndex n) :
    crossPairs n S θ⊆S×ˢ S := (Finset.filter_subset _ _).trans (fullPairs_subset n S θ)

theorem samePairs_pairwiseDisjoint (n j : ℕ) (I : Finset Point) (θ : ℤ→CapIndex n)
    (hθ : ∀ p∈I, (cap n (θ p.1)).Nonempty) :
    (Set.univ : Set (CapIndex j)).PairwiseDisjoint (fun i => samePairs (coarsePoints n j I θ i)) :=
  pairRelations_disjoint _ _ (coarsePoints_pairwiseDisjoint n j I θ hθ) (fun i => samePairs_subset _)

theorem crossPairs_pairwiseDisjoint (n j : ℕ) (I : Finset Point) (θ : ℤ→CapIndex n)
    (hθ : ∀ p∈I, (cap n (θ p.1)).Nonempty) :
    (Set.univ : Set (CapIndex j)).PairwiseDisjoint (fun i => crossPairs n (coarsePoints n j I θ i) θ) :=
  pairRelations_disjoint _ _ (coarsePoints_pairwiseDisjoint n j I θ hθ) (fun i => crossPairs_subset _ _ _)

theorem fullPairs_same (n : ℕ) (S : Finset Point) (θ : ℤ → CapIndex n) :
    (fullPairs n S θ).filter (fun p => p.1.1 = p.2.1) = samePairs S := by
  ext p
  simp only [fullPairs, samePairs, Finset.mem_filter]
  constructor
  · exact fun h => ⟨h.1.1,h.2⟩
  · exact fun h => ⟨⟨h.1,congrArg θ h.2⟩,h.2⟩

theorem quadratic_split (n : ℕ) (S : Finset Point) (θ : ℤ → CapIndex n)
    (g : Point → Space → ℂ) (x : Space) :
    pairSum (fullPairs n S θ) g x = pairSum (samePairs S) g x + pairSum (crossPairs n S θ) g x := by
  rw [QuadraticDecomposition.pairSum_split (fullPairs n S θ) (fun p => p.1.1=p.2.1), fullPairs_same]
  rfl

theorem samePairs_nonneg (S : Finset Point) (g : Point → Space → ℂ) (x : Space) :
    (pairSum (samePairs S) g x).im=0 ∧ 0≤(pairSum (samePairs S) g x).re :=
  QuadraticDecomposition.grouped_pairSum_real_nonneg S Prod.fst g x

theorem fullPairs_nonneg (n : ℕ) (S : Finset Point) (θ : ℤ → CapIndex n)
    (g : Point → Space → ℂ) (x : Space) :
    (pairSum (fullPairs n S θ) g x).im=0 ∧ 0≤(pairSum (fullPairs n S θ) g x).re :=
  QuadraticDecomposition.grouped_pairSum_real_nonneg S (fun p => θ p.1) g x

theorem groupedSquare_restrict {β : Type*} [DecidableEq β]
    (I : Finset Point) (c : Point → β) (J : Finset β) (g : Point → Space → ℂ) (x : Space) :
    FirstMass.groupedSquare (I.filter (fun p => c p ∈ J)) c g x =
      ∑ b ∈ J, ‖∑ p ∈ I.filter (fun p => c p=b), g p x‖^2 := by
  classical
  let S := I.filter (fun p => c p ∈ J)
  have hsub : S.image c ⊆ J := by
    intro b hb
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hb
    exact (Finset.mem_filter.mp hp).2
  have hf (b : β) (hb : b∈J) : S.filter (fun p => c p=b) = I.filter (fun p => c p=b) := by
    ext p
    simp only [S, Finset.mem_filter]
    constructor
    · exact fun h => ⟨h.1.1,h.2⟩
    · intro h
      exact ⟨⟨h.1,h.2 ▸ hb⟩,h.2⟩
  change (∑ b ∈ S.image c, ‖∑ p ∈ S.filter (fun p => c p=b), g p x‖^2) = _
  calc
    _ = ∑ b ∈ S.image c, ‖∑ p ∈ I.filter (fun p => c p=b), g p x‖^2 :=
      Finset.sum_congr rfl (fun b hb => by rw [hf b (hsub hb)])
    _ = _ := by
      apply Finset.sum_subset hsub
      intro b hb hn
      have he : I.filter (fun p => c p=b) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro p hp
        obtain ⟨hp,hcp⟩ := Finset.mem_filter.mp hp
        apply hn
        exact Finset.mem_image.mpr ⟨p,Finset.mem_filter.mpr ⟨hp,hcp ▸ hb⟩,hcp⟩
      simp [he]

theorem partialSquare_eq_grouped (n j : ℕ) (I : Finset Point) (θ : ℤ → CapIndex n)
    (g : Point → Space → ℂ) (f : Space → ℂ)
    (hsharp : ∀ b x, capFunction n b f x = ∑ p ∈ I.filter (fun p => θ p.1=b), g p x)
    (i : CapIndex j) (x : Space) :
    partialSquare n j i f x =
      FirstMass.groupedSquare (coarsePoints n j I θ i) (fun p => θ p.1) g x := by
  rw [coarsePoints, groupedSquare_restrict]
  simp only [partialSquare, hsharp]

theorem partialSquare_eq_fullPairs (n j : ℕ) (I : Finset Point) (θ : ℤ → CapIndex n)
    (g : Point → Space → ℂ) (f : Space → ℂ)
    (hsharp : ∀ b x, capFunction n b f x = ∑ p ∈ I.filter (fun p => θ p.1=b), g p x)
    (i : CapIndex j) (x : Space) :
    partialSquare n j i f x = (pairSum (fullPairs n (coarsePoints n j I θ i) θ) g x).re := by
  rw [partialSquare_eq_grouped n j I θ g f hsharp, FirstMass.groupedSquare_pairSum]
  rfl

def sameMass (n j : ℕ) (I : Finset Point) (θ : ℤ → CapIndex n)
    (g : Point → Space → ℂ) (i : CapIndex j) (m : Lattice) : ℝ :=
  (∫ x, (pairSum (samePairs (coarsePoints n j I θ i)) g x).re*envelopeWeight n j i m x)/
    envelopeVolume n j i m

theorem sameMass_nonneg (n j : ℕ) (I : Finset Point) (θ : ℤ → CapIndex n)
    (g : Point → Space → ℂ) (i : CapIndex j) (m : Lattice) :
    0 ≤ sameMass n j I θ g i m := by
  exact div_nonneg (integral_nonneg (fun x =>
    mul_nonneg (samePairs_nonneg _ g x).2 (envelopeWeight_nonneg n j i m x)))
    (WeightMass.envelopeVolume_pos n j i m).le

theorem average_re (w : Space→ℝ) (V : ℝ) (g : Space→ℂ)
    (hg : Integrable (fun x => (w x : ℂ)*g x)) :
    (CountableAveraging.average volume w V g).re = (∫ x, (g x).re*w x)/V := by
  have hi : (∫ x, (g x).re*w x) = (∫ x, (w x : ℂ)*g x).re := by
    have hh := integral_re hg
    change (∫ x, ((w x : ℂ)*g x).re) = (∫ x, (w x : ℂ)*g x).re at hh
    simp only [Complex.re_ofReal_mul] at hh
    rw [← hh]
    apply integral_congr_ae
    filter_upwards with x
    ring
  rw [CountableAveraging.average, ← Complex.ofReal_inv, Complex.re_ofReal_mul, hi]
  ring

theorem sameMass_eq_average_re (n j : ℕ) (I : Finset Point) (θ : ℤ → CapIndex n)
    (g : Point→Space→ℂ) (i : CapIndex j) (m : Lattice)
    (hi : Integrable (fun x => (envelopeWeight n j i m x : ℂ)*
      pairSum (samePairs (coarsePoints n j I θ i)) g x)) :
    sameMass n j I θ g i m =
      (CountableAveraging.average volume (envelopeWeight n j i m) (envelopeVolume n j i m)
        (pairSum (samePairs (coarsePoints n j I θ i)) g)).re :=
  (average_re _ _ _ hi).symm

theorem localMass_eq_average_re (n j : ℕ) (I : Finset Point) (θ : ℤ → CapIndex n)
    (g : Point→Space→ℂ) (f : Space→ℂ)
    (hsharp : ∀ b x, capFunction n b f x = ∑ p∈I.filter (fun p => θ p.1=b), g p x)
    (i : CapIndex j) (m : Lattice)
    (hi : Integrable (fun x => (envelopeWeight n j i m x : ℂ)*
      pairSum (fullPairs n (coarsePoints n j I θ i) θ) g x)) :
    localMass n j i m f =
      (CountableAveraging.average volume (envelopeWeight n j i m) (envelopeVolume n j i m)
        (pairSum (fullPairs n (coarsePoints n j I θ i) θ) g)).re := by
  rw [average_re _ _ _ hi, localMass]
  simp_rw [partialSquare_eq_fullPairs n j I θ g f hsharp]

theorem average_pairSum_split (n j : ℕ) (S : Finset Point) (θ : ℤ → CapIndex n)
    (g : Point→Space→ℂ) (i : CapIndex j) (m : Lattice)
    (hs : Integrable (fun x => (envelopeWeight n j i m x : ℂ)*pairSum (samePairs S) g x))
    (hc : Integrable (fun x => (envelopeWeight n j i m x : ℂ)*pairSum (crossPairs n S θ) g x)) :
    CountableAveraging.average volume (envelopeWeight n j i m) (envelopeVolume n j i m)
      (pairSum (fullPairs n S θ) g) =
    CountableAveraging.average volume (envelopeWeight n j i m) (envelopeVolume n j i m)
      (pairSum (samePairs S) g) +
    CountableAveraging.average volume (envelopeWeight n j i m) (envelopeVolume n j i m)
      (pairSum (crossPairs n S θ) g) := by
  simp only [CountableAveraging.average, quadratic_split, mul_add]
  rw [integral_add hs hc]
  ring

theorem localMass_sub_sameMass (n j : ℕ) (I : Finset Point) (θ : ℤ → CapIndex n)
    (g : Point→Space→ℂ) (f : Space→ℂ)
    (hsharp : ∀ b x, capFunction n b f x = ∑ p∈I.filter (fun p => θ p.1=b), g p x)
    (i : CapIndex j) (m : Lattice)
    (hi : ∀ F : Finset Pair, Integrable (fun x => (envelopeWeight n j i m x : ℂ)*pairSum F g x)) :
    localMass n j i m f - sameMass n j I θ g i m =
      (CountableAveraging.average volume (envelopeWeight n j i m) (envelopeVolume n j i m)
        (pairSum (crossPairs n (coarsePoints n j I θ i) θ) g)).re := by
  rw [localMass_eq_average_re n j I θ g f hsharp i m (hi _),
    sameMass_eq_average_re n j I θ g i m (hi _),
    average_pairSum_split n j _ θ g i m (hi _) (hi _), Complex.add_re]
  ring

end
end CircleDivisor.EnergyV3.CoarseDecomposition
