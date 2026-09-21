import CircleDivisor.EnergyV3.WeightOverlap
import CircleDivisor.EnergyV3.CountableAveraging

/-! Mass and averaging for the actual canonical envelopes. The coordinate map
is an actual invertible linear map; its Jacobian multiplies both the weight
integral and the envelope volume, so the normalized masses agree exactly. -/

namespace CircleDivisor.EnergyV3.WeightMass
noncomputable section
open MeasureTheory MeasureTheory.Measure GuthMaldague
open scoped RealInnerProductSpace BigOperators
set_option maxHeartbeats 1200000

def coordinateLinear (R s ω : ℝ) : Space →ₗ[ℝ] Space where
  toFun x := WithLp.toLp 2 (envelopeCoordinates R s ω x)
  map_add' x y := by
    ext k
    fin_cases k <;> simp [envelopeCoordinates, inner_add_right, add_div]
  map_smul' c x := by
    ext k
    fin_cases k <;> simp [envelopeCoordinates, inner_smul_right] <;> ring

theorem coordinate_surjective (R s ω : ℝ) (hR : R ≠ 0) (hs : s ≠ 0) :
    Function.Surjective (coordinateLinear R s ω) := by
  intro u
  refine ⟨envelopeSynthesis R s ω (fun k => u k), ?_⟩
  change WithLp.toLp 2 (envelopeCoordinates R s ω _) = u
  rw [envelopeCoordinates_synthesis R s ω hR hs]

def coordinateEquiv (R s ω : ℝ) (hR : R ≠ 0) (hs : s ≠ 0) : Space ≃L[ℝ] Space :=
  (LinearEquiv.ofBijective (coordinateLinear R s ω)
    ⟨(LinearMap.injective_iff_surjective).mpr (coordinate_surjective R s ω hR hs),
      coordinate_surjective R s ω hR hs⟩).toContinuousLinearEquiv

def unitCube : Set Space := {u | ∀ k, |u k| ≤ 1 / 2}

theorem unitCube_volume : volume unitCube = 1 := by
  let e := (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm
  have hp := EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3)
  have he : unitCube = e ⁻¹' Set.pi Set.univ (fun _ : Fin 3 => Set.Icc (-(1 / 2 : ℝ)) (1 / 2)) := by
    ext x
    simp [unitCube, e, abs_le, Pi.le_def, forall_and]
  rw [he, hp.measure_preimage (by measurability)]
  norm_num [Real.volume_Icc_pi]

def jacobian (R s ω : ℝ) (hR : R ≠ 0) (hs : s ≠ 0) : ℝ :=
  |LinearMap.det ((coordinateEquiv R s ω hR hs).symm : Space →ₗ[ℝ] Space)|

theorem jacobian_pos (R s ω : ℝ) (hR : R ≠ 0) (hs : s ≠ 0) :
    0 < jacobian R s ω hR hs := by
  apply abs_pos.mpr
  exact (LinearEquiv.isUnit_det' (coordinateEquiv R s ω hR hs).symm.toLinearEquiv).ne_zero

theorem coordinate_map (R s ω : ℝ) (hR : R ≠ 0) (hs : s ≠ 0) :
    Measure.map (coordinateEquiv R s ω hR hs) volume =
      ENNReal.ofReal (jacobian R s ω hR hs) • volume := by
  let e := coordinateEquiv R s ω hR hs
  change Measure.map (e : Space →ₗ[ℝ] Space) volume = _
  rw [map_linearMap_addHaar_eq_smul_addHaar (f := (e : Space →ₗ[ℝ] Space)) volume
    (LinearEquiv.isUnit_det' e.toLinearEquiv).ne_zero]
  congr 2
  exact (congrArg abs (LinearEquiv.det_coe_symm e.toLinearEquiv)).symm

theorem envelope_volume (n j : ℕ) (i : CapIndex j) (m : Lattice) :
    volume (envelope n j i m) =
      ENNReal.ofReal (jacobian (radius n) (scale j) (leftEndpoint j i)
        (radius_pos n).ne' (scale_pos j).ne') := by
  let e := coordinateEquiv (radius n) (scale j) (leftEndpoint j i)
    (radius_pos n).ne' (scale_pos j).ne'
  have he : envelope n j i m =
      (fun x => x + (-envelopeCenter n j i m)) ⁻¹' (e ⁻¹' unitCube) := by
    ext x
    rfl
  rw [he, measure_preimage_add_right, addHaar_preimage_continuousLinearEquiv,
    unitCube_volume, mul_one]
  rfl

theorem envelopeVolume_eq (n j : ℕ) (i : CapIndex j) (m : Lattice) :
    envelopeVolume n j i m = jacobian (radius n) (scale j) (leftEndpoint j i)
      (radius_pos n).ne' (scale_pos j).ne' := by
  unfold envelopeVolume Measure.real
  rw [envelope_volume, ENNReal.toReal_ofReal (jacobian_pos _ _ _ _ _).le]

theorem envelopeVolume_pos (n j : ℕ) (i : CapIndex j) (m : Lattice) :
    0 < envelopeVolume n j i m := by rw [envelopeVolume_eq]; exact jacobian_pos _ _ _ _ _

theorem envelopeWeight_integrable (n j : ℕ) (i : CapIndex j) (m : Lattice) :
    Integrable (envelopeWeight n j i m) := by
  let e := coordinateEquiv (radius n) (scale j) (leftEndpoint j i)
    (radius_pos n).ne' (scale_pos j).ne'
  let w : Space → ℝ := fun u => baseWeight u / weightNormalization
  have hw : Integrable w := baseWeight_integrable.div_const _
  have hmap : Integrable w (Measure.map e volume) := by
    rw [coordinate_map]
    exact hw.smul_measure ENNReal.ofReal_ne_top
  have he : Integrable (w ∘ e) := hmap.comp_measurable e.continuous.measurable
  have htrans := (measurePreserving_add_right volume (-envelopeCenter n j i m)).integrable_comp_of_integrable he
  exact htrans

theorem envelopeWeight_mass (n j : ℕ) (i : CapIndex j) (m : Lattice) :
    (∫ x, envelopeWeight n j i m x) = envelopeVolume n j i m := by
  let e := coordinateEquiv (radius n) (scale j) (leftEndpoint j i)
    (radius_pos n).ne' (scale_pos j).ne'
  let w : Space → ℝ := fun u => baseWeight u / weightNormalization
  change (∫ x, w (e (x - envelopeCenter n j i m))) = _
  rw [integral_sub_right_eq_self (fun x => w (e x))]
  have ht := e.toHomeomorph.toMeasurableEquiv.measurableEmbedding.integral_map (μ := volume) w
  change (∫ u, w u ∂Measure.map e volume) = ∫ x, w (e x) at ht
  rw [← ht, coordinate_map,
    integral_smul_measure, ENNReal.toReal_ofReal (jacobian_pos _ _ _ _ _).le]
  have hw : (∫ u, w u) = 1 := normalizedWeight_integral
  rw [hw, smul_eq_mul, mul_one, envelopeVolume_eq]

theorem actual_countable_averaging (n j : ℕ) (i : CapIndex j)
    (g : Space → ℂ) (hg : MemLp g 2 volume) :
    (∀ m : Lattice, Integrable (fun x => (envelopeWeight n j i m x : ℂ) * g x)) ∧
    Summable (fun m : Lattice => envelopeVolume n j i m *
      ‖CountableAveraging.average volume (envelopeWeight n j i m) (envelopeVolume n j i m) g‖ ^ 2) ∧
    (∑' m : Lattice, envelopeVolume n j i m *
      ‖CountableAveraging.average volume (envelopeWeight n j i m) (envelopeVolume n j i m) g‖ ^ 2) ≤
        ((4 * WeightOverlap.overlapConstant) ^ 3 / weightNormalization) * ∫ x, ‖g x‖ ^ 2 := by
  simpa only [one_mul] using CountableAveraging.countable_averaging
    (envelopeWeight n j i) (envelopeVolume n j i) g 1
    ((4 * WeightOverlap.overlapConstant) ^ 3 / weightNormalization) hg (by norm_num)
    (envelopeWeight_integrable n j i) (envelopeWeight_nonneg n j i)
    (envelopeVolume_pos n j i) (fun m => by rw [one_mul]; exact envelopeWeight_mass n j i m)
    (WeightOverlap.actual_envelope_finite_overlap n j i)

end
end CircleDivisor.EnergyV3.WeightMass
