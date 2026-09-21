import CircleDivisor.FourierLocalization

/-!
# The concrete Guth--Maldague external input

Source: Guth--Maldague, arXiv:2206.01093v2, Theorem 2, Section 5 (29),
its frame/envelope definitions, and the weight (13) in Section 2.
https://arxiv.org/html/2206.01093v2

`GuthMaldagueInput` is a theorem *statement*, not an axiom or a proved theorem.
It is the positive-sheet specialization needed by the manuscript. All geometric
and analytic objects are defined here: dyadic caps, sharp Fourier projections,
the frame, the integer translate lattice, the product-decay weight, local mass,
active-cap count, and the nonnegative countable envelope sum. It does not assume
any of the manuscript's local density, orthogonality, or energy conclusions.

The displayed weight in the source is accompanied by L1 normalization. We make
that suppressed fixed normalization constant explicit by dividing by its integral.
Closed envelope boxes may share boundaries, as in the source's translation tiling.
-/

namespace CircleDivisor.GuthMaldague
noncomputable section
open MeasureTheory FourierTransform
open scoped BigOperators RealInnerProductSpace SchwartzMap NNReal ENNReal

abbrev Space := EuclideanSpace ℝ (Fin 3)
abbrev Lattice := Fin 3 → ℤ

def radius (n : ℕ) : ℝ := 4 ^ n
def scale (j : ℕ) : ℝ := ((2 : ℝ) ^ j)⁻¹
abbrev CapIndex (j : ℕ) := Fin (2 ^ j)

theorem radius_pos (n : ℕ) : 0 < radius n := by unfold radius; positivity
theorem scale_pos (j : ℕ) : 0 < scale j := by unfold scale; positivity

theorem scale_sq_eq_radius_inv (n : ℕ) : scale n ^ 2 = (radius n)⁻¹ := by
  have h : ((2 : ℝ) ^ n) ^ 2 = (4 : ℝ) ^ n := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  simpa [scale, radius] using congrArg Inv.inv h

/-- The positive sheet of the radial truncation used in Section 5. -/
def cone : Set Space := {ξ | ξ 0 ^ 2 + ξ 1 ^ 2 = ξ 2 ^ 2 ∧
  (1 / 2 : ℝ) ≤ ξ 2 ∧ ξ 2 ≤ 2}

def coneNeighborhood (δ : ℝ) : Set Space :=
  {ξ | ∃ η ∈ cone, dist ξ η < δ}

/-- Cylindrical angle in `[0,2π)`. The value on the vertical axis is immaterial
for sufficiently small neighborhoods of the truncated cone. -/
def cylindricalAngle (ξ : Space) : ℝ :=
  let t := Complex.arg ((ξ 0 : ℂ) + (ξ 1 : ℂ) * Complex.I)
  if t < 0 then t + 2 * Real.pi else t

def leftEndpoint (j : ℕ) (i : CapIndex j) : ℝ :=
  2 * Real.pi * (i.val : ℝ) * scale j

def angularInterval (j : ℕ) (i : CapIndex j) : Set ℝ :=
  Set.Ico (leftEndpoint j i) (leftEndpoint j i + 2 * Real.pi * scale j)

/-- The actual `s`-cap: the angular sector inside the `s²` cone neighborhood. -/
def cap (j : ℕ) (i : CapIndex j) : Set Space :=
  coneNeighborhood (scale j ^ 2) ∩ cylindricalAngle ⁻¹' angularInterval j i

/-- `f_tau` is a sharp Fourier restriction, not an unspecified component. -/
def capFunction (j : ℕ) (i : CapIndex j) (f : Space → ℂ) : Space → ℂ :=
  FourierLocalization.sharpProjection (cap j i) f

def fineChildren (n j : ℕ) (i : CapIndex j) : Finset (CapIndex n) := by
  classical
  exact Finset.univ.filter (fun b => cap n b ⊆ cap j i)

def frameC (ω : ℝ) : Space := WithLp.toLp 2 ![Real.cos ω, Real.sin ω, 1]
def frameT (ω : ℝ) : Space := WithLp.toLp 2 ![-Real.sin ω, Real.cos ω, 0]
def frameN (ω : ℝ) : Space := WithLp.toLp 2 ![Real.cos ω, Real.sin ω, -1]

theorem frame_inner_values (ω : ℝ) :
    ⟪frameC ω, frameC ω⟫ = 2 ∧ ⟪frameT ω, frameT ω⟫ = 1 ∧
    ⟪frameN ω, frameN ω⟫ = 2 ∧ ⟪frameC ω, frameT ω⟫ = 0 ∧
    ⟪frameC ω, frameN ω⟫ = 0 ∧ ⟪frameT ω, frameN ω⟫ = 0 := by
  simp only [frameC, frameT, frameN, PiLp.inner_apply]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [Fin.sum_univ_succ] <;> nlinarith [Real.sin_sq_add_cos_sq ω]

/-- Coordinates mapping the source's centered envelope to `[-1/2,1/2]^3`.
The generator and normal frame vectors have squared norm two. -/
def envelopeCoordinates (R s ω : ℝ) (x : Space) : Fin 3 → ℝ :=
  ![⟪frameC ω, x⟫ / (2 * R * s ^ 2),
    ⟪frameT ω, x⟫ / (2 * R * s), ⟪frameN ω, x⟫ / (2 * R)]

/-- Inverse coordinate formula; its values on integer vectors are the
translation lattice of the source's envelopes. -/
def envelopeSynthesis (R s ω : ℝ) (u : Fin 3 → ℝ) : Space :=
  (R * s ^ 2 * u 0) • frameC ω + (2 * R * s * u 1) • frameT ω +
    (R * u 2) • frameN ω

theorem envelopeCoordinates_synthesis (R s ω : ℝ) (hR : R ≠ 0) (hs : s ≠ 0)
    (u : Fin 3 → ℝ) :
    envelopeCoordinates R s ω (envelopeSynthesis R s ω u) = u := by
  rcases frame_inner_values ω with ⟨hcc, htt, hnn, hct, hcn, htn⟩
  have htc : ⟪frameT ω, frameC ω⟫ = 0 := by rw [real_inner_comm, hct]
  have hnc : ⟪frameN ω, frameC ω⟫ = 0 := by rw [real_inner_comm, hcn]
  have hnt : ⟪frameN ω, frameT ω⟫ = 0 := by rw [real_inner_comm, htn]
  simp only [real_inner_self_eq_norm_sq] at hcc htt hnn
  funext k
  fin_cases k <;>
    simp [envelopeCoordinates, envelopeSynthesis, inner_add_right, inner_smul_right,
      hcc, htt, hnn, hct, hcn, htn, htc, hnc, hnt, hR, hs] <;> field_simp

theorem envelopeCoordinates_sub (R s ω : ℝ) (x y : Space) :
    envelopeCoordinates R s ω (x - y) =
      fun k => envelopeCoordinates R s ω x k - envelopeCoordinates R s ω y k := by
  funext k
  fin_cases k <;> simp [envelopeCoordinates, inner_sub_right, sub_div]

def envelopeCenter (n j : ℕ) (i : CapIndex j) (m : Lattice) : Space :=
  envelopeSynthesis (radius n) (scale j) (leftEndpoint j i) (fun k => (m k : ℝ))

def centeredEnvelope (n j : ℕ) (i : CapIndex j) : Set Space :=
  {x | ∀ k, |envelopeCoordinates (radius n) (scale j) (leftEndpoint j i) x k| ≤ 1 / 2}

def envelope (n j : ℕ) (i : CapIndex j) (m : Lattice) : Set Space :=
  {x | x - envelopeCenter n j i m ∈ centeredEnvelope n j i}

theorem mem_envelope_iff (n j : ℕ) (i : CapIndex j) (m : Lattice) (x : Space) :
    x ∈ envelope n j i m ↔ ∀ k,
      |envelopeCoordinates (radius n) (scale j) (leftEndpoint j i) x k - (m k : ℝ)| ≤ 1 / 2 := by
  simp only [envelope, centeredEnvelope, Set.mem_setOf_eq, envelopeCoordinates_sub,
    envelopeCenter, envelopeCoordinates_synthesis _ _ _ (radius_pos n).ne' (scale_pos j).ne']

/-- The explicitly defined integer lattice really covers physical space by
translates of the exact source envelope. Boundaries may be shared. -/
theorem envelope_cover (n j : ℕ) (i : CapIndex j) (x : Space) :
    ∃ m : Lattice, x ∈ envelope n j i m := by
  let u := envelopeCoordinates (radius n) (scale j) (leftEndpoint j i) x
  let m : Lattice := fun k => ⌊u k + 1 / 2⌋
  refine ⟨m, (mem_envelope_iff n j i m x).mpr ?_⟩
  intro k
  have hl := Int.floor_le (u k + 1 / 2)
  have hu := Int.lt_floor_add_one (u k + 1 / 2)
  change |u k - (m k : ℝ)| ≤ 1 / 2
  change (m k : ℝ) ≤ u k + 1 / 2 at hl
  change u k + 1 / 2 < (m k : ℝ) + 1 at hu
  exact abs_le.mpr ⟨by linarith, by linarith⟩

def envelopeVolume (n j : ℕ) (i : CapIndex j) (m : Lattice) : ℝ :=
  volume.real (envelope n j i m)

def baseWeight (u : Space) : ℝ := ∏ k : Fin 3, ((1 + (u k) ^ 2) ^ 100)⁻¹

theorem baseWeight_nonneg (u : Space) : 0 ≤ baseWeight u := by
  unfold baseWeight
  positivity

theorem baseWeight_pos (u : Space) : 0 < baseWeight u := by
  unfold baseWeight
  positivity

theorem baseWeight_continuous : Continuous baseWeight := by
  unfold baseWeight
  fun_prop (disch := first | positivity | intro x; positivity)

theorem baseWeight_integrable : Integrable baseWeight := by
  have h1 : Integrable (fun x : ℝ => ((1 + x ^ 2) ^ 100)⁻¹) := by
    have hh := integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume)
      (r := 200) (by norm_num)
    convert hh using 1
    funext x
    rw [show -(200 : ℝ) / 2 = -(100 : ℝ) by norm_num, Real.rpow_neg]
    simp only [Real.norm_eq_abs, sq_abs]
    congr 1
    exact (Real.rpow_natCast _ 100).symm
    all_goals positivity
  have hpi : Integrable (fun u : Fin 3 → ℝ => ∏ k : Fin 3, ((1 + (u k) ^ 2) ^ 100)⁻¹) :=
    Integrable.fintype_prod (fun _ : Fin 3 => h1)
  have hp := (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3)).integrable_comp_emb
    (MeasurableEquiv.measurableEmbedding _) (g := fun u : Fin 3 → ℝ =>
      ∏ k : Fin 3, ((1 + (u k) ^ 2) ^ 100)⁻¹)
  exact hp.mpr hpi

def weightNormalization : ℝ := ∫ u : Space, baseWeight u

theorem weightNormalization_pos : 0 < weightNormalization := by
  exact integral_pos_of_integrable_nonneg_nonzero baseWeight_continuous
    baseWeight_integrable baseWeight_nonneg (ne_of_gt (baseWeight_pos 0))

def normalizedWeight (u : Fin 3 → ℝ) : ℝ :=
  baseWeight (WithLp.toLp 2 u) / weightNormalization

theorem normalizedWeight_nonneg (u : Fin 3 → ℝ) : 0 ≤ normalizedWeight u :=
  div_nonneg (baseWeight_nonneg _) (integral_nonneg baseWeight_nonneg)

theorem normalizedWeight_integral :
    (∫ u : Space, normalizedWeight (fun k => u k)) = 1 := by
  change (∫ u : Space, baseWeight u / weightNormalization) = 1
  rw [integral_div]
  exact div_self weightNormalization_pos.ne'

def envelopeWeight (n j : ℕ) (i : CapIndex j) (m : Lattice) (x : Space) : ℝ :=
  normalizedWeight (envelopeCoordinates (radius n) (scale j) (leftEndpoint j i)
    (x - envelopeCenter n j i m))

theorem envelopeWeight_nonneg (n j : ℕ) (i : CapIndex j) (m : Lattice) (x : Space) :
    0 ≤ envelopeWeight n j i m x := normalizedWeight_nonneg _

def partialSquare (n j : ℕ) (i : CapIndex j) (f : Space → ℂ) (x : Space) : ℝ :=
  ∑ b ∈ fineChildren n j i, ‖capFunction n b f x‖ ^ 2

theorem partialSquare_nonneg (n j : ℕ) (i : CapIndex j) (f : Space → ℂ) (x : Space) :
    0 ≤ partialSquare n j i f x := by unfold partialSquare; positivity

/-- Exactly `|U|⁻¹ ∥S_U f∥₂²`, expressed by its nonnegative integral. -/
def localMass (n j : ℕ) (i : CapIndex j) (m : Lattice) (f : Space → ℂ) : ℝ :=
  (∫ x, partialSquare n j i f x * envelopeWeight n j i m x) /
    envelopeVolume n j i m

theorem localMass_nonneg (n j : ℕ) (i : CapIndex j) (m : Lattice) (f : Space → ℂ) :
    0 ≤ localMass n j i m f := by
  apply div_nonneg
  · exact integral_nonneg (fun x => mul_nonneg (partialSquare_nonneg n j i f x)
      (envelopeWeight_nonneg n j i m x))
  · exact ENNReal.toReal_nonneg

def activeCaps (j : ℕ) (f : Space → ℂ) : Finset (CapIndex j) := by
  classical
  exact Finset.univ.filter (fun i => capFunction j i f ≠ 0)

def activeCount (j : ℕ) (f : Space → ℂ) : ℕ := (activeCaps j f).card

theorem activeCount_le (j : ℕ) (f : Space → ℂ) : activeCount j f ≤ 2 ^ j := by
  classical
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by simp)

/-- The source's amplitude threshold, multiplied by the squared active count.
For positive amplitude this automatically excludes zero active-count scales. -/
def contributing (C ε α : ℝ) (n j : ℕ) (i : CapIndex j) (m : Lattice)
    (f : Space → ℂ) : Prop :=
  α ^ 2 ≤ C * (radius n) ^ ε * (activeCount j f : ℝ) ^ 2 * localMass n j i m f

/-- The active count really yields the manuscript's `α² s²` lower threshold.
No count of fine caps inside one coarse cap is substituted here. -/
theorem contributing_mass_threshold (C ε α : ℝ) (hC : 0 ≤ C)
    (n j : ℕ) (i : CapIndex j) (m : Lattice) (f : Space → ℂ)
    (hgood : contributing C ε α n j i m f) :
    α ^ 2 * scale j ^ 2 ≤ C * (radius n) ^ ε * localMass n j i m f := by
  have hn : (activeCount j f : ℝ) ≤ (2 : ℝ) ^ j := by exact_mod_cast activeCount_le j f
  have hn0 : 0 ≤ (activeCount j f : ℝ) := Nat.cast_nonneg _
  have hm := localMass_nonneg n j i m f
  have hfactor : 0 ≤ C * (radius n) ^ ε := mul_nonneg hC (Real.rpow_nonneg (radius_pos n).le _)
  have hb := mul_le_mul_of_nonneg_right hgood (sq_nonneg (scale j))
  calc
    _ ≤ (C * (radius n) ^ ε * (activeCount j f : ℝ) ^ 2 * localMass n j i m f) * scale j ^ 2 := hb
    _ ≤ (C * (radius n) ^ ε * ((2 : ℝ) ^ j) ^ 2 * localMass n j i m f) * scale j ^ 2 := by
      gcongr
    _ = _ := by
      unfold scale
      field_simp

/-- An ENNReal tsum retains the meaning of a nonnegative countable sum even
before its finiteness has been proved. No conditionally-convergent real tsum is used. -/
def envelopeEnergy (C ε α : ℝ) (n j : ℕ) (i : CapIndex j) (f : Space → ℂ) : ℝ≥0∞ := by
  classical
  exact ∑' m : Lattice, if contributing C ε α n j i m f then
    ENNReal.ofReal (envelopeVolume n j i m * localMass n j i m f ^ 2) else 0

def waveEnvelopeSum (C ε α : ℝ) (n : ℕ) (f : Space → ℂ) : ℝ≥0∞ :=
  ∑ j ∈ Finset.Ioo 0 n, ∑ i : CapIndex j, envelopeEnergy C ε α n j i f

/-- The explicit external theorem statement. The fixed positive-sheet
specialization and the fixed weight normalization are stated in this file's header.
The constant and sufficiently-large threshold precede every `n`, `f`, and `α`. -/
def GuthMaldagueInput : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    ∀ f : 𝓢(Space, ℂ), tsupport (𝓕 (f : Space → ℂ)) ⊆
      coneNeighborhood ((radius n)⁻¹) → ∀ α : ℝ, 0 < α →
      ENNReal.ofReal (α ^ 4) * volume {x : Space | α < ‖f x‖} ≤
        ENNReal.ofReal (C * (radius n) ^ ε) * waveEnvelopeSum C ε α n f

end
end CircleDivisor.GuthMaldague
