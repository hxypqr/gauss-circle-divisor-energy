import CircleDivisor.ExternalInterfaces

/-!
# Actual period-normalization bridge for the Li--Yang moment

The proof below uses Fubini and interval integrals, not a new external input.
In particular it removes the normalization mismatch between the source's
`[-1,1]^2` and the manuscript's `[0,1]^2` in the integer coordinates.
-/

namespace CircleDivisor.ExternalPeriodBridge
noncomputable section
open MeasureTheory
open scoped BigOperators

theorem integral_pi_insertNth {n : ℕ} (μ : Fin (n + 1) → Measure ℝ)
    [∀ i, SigmaFinite (μ i)] (i : Fin (n + 1))
    (f : (Fin (n + 1) → ℝ) → ℝ) (hf : Integrable f (Measure.pi μ)) :
    ∫ x, f x ∂Measure.pi μ =
      ∫ y, ∫ t, f (i.insertNth t y) ∂μ i ∂Measure.pi (fun j => μ (i.succAbove j)) := by
  have mp := (measurePreserving_piFinSuccAbove μ i).symm
  have he := mp.integral_comp' f
  have hi := (mp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).2 hf
  rw [← he]
  simpa only [Function.comp_def, MeasurableEquiv.piFinSuccAbove_symm_apply,
    Fin.insertNthEquiv, Equiv.coe_fn_mk] using integral_prod_symm _ hi

theorem periodic_two_periods {f : ℝ → ℝ} (hf : Continuous f)
    (hp : Function.Periodic f 1) :
    ∫ t in Set.Icc (-1 : ℝ) 1, f t = 2 * ∫ t in Set.Icc (0 : ℝ) 1, f t := by
  have h2 := hp.intervalIntegral_add_zsmul_eq (2 : ℤ) (-1)
    (fun a b => hf.intervalIntegrable a b)
  have h1 := hp.intervalIntegral_add_eq (-1) 0
  norm_num at h1 h2
  rw [h1] at h2
  simpa only [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integral_Icc_eq_integral_Ioc] using h2

theorem integral_box_two_periods {n : ℕ} (i : Fin (n + 1))
    (s : Fin n → Set ℝ) (hs : ∀ j, IsCompact (s j))
    (f : (Fin (n + 1) → ℝ) → ℝ) (hf : Continuous f)
    (hp : ∀ y, Function.Periodic (fun t => f (i.insertNth t y)) 1) :
    ∫ x in Set.pi Set.univ (i.insertNth (Set.Icc (-1 : ℝ) 1) s), f x =
      2 * ∫ x in Set.pi Set.univ (i.insertNth (Set.Icc (0 : ℝ) 1) s), f x := by
  have hint (J : Set ℝ) (hJ : IsCompact J) :
      Integrable f (Measure.pi (fun j : Fin (n + 1) =>
        (volume : Measure ℝ).restrict ((i.insertNth J s : Fin (n + 1) → Set ℝ) j))) := by
    rw [← Measure.restrict_pi_pi]
    apply hf.continuousOn.integrableOn_compact
    apply isCompact_univ_pi
    rw [i.forall_iff_succAbove]
    simpa using And.intro hJ hs
  have hsource := integral_pi_insertNth
    (fun j : Fin (n + 1) => (volume : Measure ℝ).restrict
      ((i.insertNth (Set.Icc (-1 : ℝ) 1) s : Fin (n + 1) → Set ℝ) j)) i f
    (hint _ isCompact_Icc)
  have htarget := integral_pi_insertNth
    (fun j : Fin (n + 1) => (volume : Measure ℝ).restrict
      ((i.insertNth (Set.Icc (0 : ℝ) 1) s : Fin (n + 1) → Set ℝ) j)) i f
    (hint _ isCompact_Icc)
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove] at hsource htarget
  change (∫ x, f x ∂(Measure.pi (fun _ : Fin (n + 1) => (volume : Measure ℝ))).restrict _) =
    2 * (∫ x, f x ∂(Measure.pi (fun _ : Fin (n + 1) => (volume : Measure ℝ))).restrict _)
  rw [Measure.restrict_pi_pi, Measure.restrict_pi_pi, hsource, htarget]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with y
  apply periodic_two_periods
  · have ht : Continuous (fun t : ℝ => (i.insertNth t y : Fin (n + 1) → ℝ)) := by
      fun_prop
    exact hf.comp ht
  · exact hp y

open ExternalInterfaces

theorem moment_periodic_insertNth_zero (K L q : ℝ) (a : ℤ → ℤ → ℂ)
    (y : Fin 2 → ℝ) :
    Function.Periodic (fun t => ‖coneSum K L a ((0 : Fin 3).insertNth t y)‖ ^ q) 1 := by
  intro t
  let x : Fin 3 → ℝ := (0 : Fin 3).insertNth t y
  have h := coneSum_integer_periods K L a (1 : ℤ) (0 : ℤ) x
  have he : (fun i => if i = 0 then x i + (1 : ℝ)
      else if i = 1 then x i + (0 : ℝ)
      else x i) = (0 : Fin 3).insertNth (t + 1) y := by
    ext i
    fin_cases i <;> simp [x, Fin.insertNth, Fin.succAboveCases]
    rfl
  simp only [Int.cast_one, Int.cast_zero] at h
  rw [he] at h
  exact congrArg (fun z : ℂ => ‖z‖ ^ q) h

theorem moment_periodic_insertNth_one (K L q : ℝ) (a : ℤ → ℤ → ℂ)
    (y : Fin 2 → ℝ) :
    Function.Periodic (fun t => ‖coneSum K L a ((1 : Fin 3).insertNth t y)‖ ^ q) 1 := by
  intro t
  let x : Fin 3 → ℝ := (1 : Fin 3).insertNth t y
  have h := coneSum_integer_periods K L a (0 : ℤ) (1 : ℤ) x
  have he : (fun i => if i = 0 then x i + (0 : ℝ)
      else if i = 1 then x i + (1 : ℝ)
      else x i) = (1 : Fin 3).insertNth (t + 1) y := by
    ext i
    fin_cases i <;> simp [x, Fin.insertNth, Fin.succAboveCases]
  simp only [Int.cast_one, Int.cast_zero] at h
  rw [he] at h
  exact congrArg (fun z : ℂ => ‖z‖ ^ q) h

def periodBox (u v d : ℝ) : Set (Fin 3 → ℝ) :=
  Set.pi Set.univ ![Set.Icc u 1, Set.Icc v 1, Set.Icc (-d) d]

theorem integral_periodBox (K L q d : ℝ) (hq : 0 ≤ q) (a : ℤ → ℤ → ℂ) :
    ∫ x in periodBox (-1) (-1) d, ‖coneSum K L a x‖ ^ q =
      4 * ∫ x in periodBox 0 0 d, ‖coneSum K L a x‖ ^ q := by
  have hc := (Real.continuous_rpow_const hq).comp (coneSum_continuous K L a).norm
  have hs₀ : ∀ j : Fin 2, IsCompact (![Set.Icc (-1 : ℝ) 1, Set.Icc (-d) d] j) := by
    intro j
    fin_cases j <;> exact isCompact_Icc
  have hs₁ : ∀ j : Fin 2, IsCompact (![Set.Icc (0 : ℝ) 1, Set.Icc (-d) d] j) := by
    intro j
    fin_cases j <;> exact isCompact_Icc
  have h₀ := integral_box_two_periods (0 : Fin 3) _ hs₀
    (fun x => ‖coneSum K L a x‖ ^ q) hc (moment_periodic_insertNth_zero K L q a)
  have h₁ := integral_box_two_periods (1 : Fin 3) _ hs₁
    (fun x => ‖coneSum K L a x‖ ^ q) hc (moment_periodic_insertNth_one K L q a)
  have e₀ (J : Set ℝ) : (0 : Fin 3).insertNth J
      ![Set.Icc (-1 : ℝ) 1, Set.Icc (-d) d] = ![J, Set.Icc (-1) 1, Set.Icc (-d) d] := by
    ext i
    fin_cases i <;> rfl
  have e₁ (J : Set ℝ) : (1 : Fin 3).insertNth J
      ![Set.Icc (0 : ℝ) 1, Set.Icc (-d) d] = ![Set.Icc 0 1, J, Set.Icc (-d) d] := by
    ext i
    fin_cases i <;> rfl
  simp only [e₀] at h₀
  simp only [e₁] at h₁
  unfold periodBox
  rw [h₀, h₁]
  ring

theorem etaSourceMoment_eq_etaMoment (K L η q : ℝ) (hq : 0 ≤ q)
    (a : ℤ → ℤ → ℂ) : etaSourceMoment K L η q a = etaMoment K L η q a := by
  have eS : etaSourceBox K L η = periodBox (-1) (-1) ((η * L * Real.sqrt K)⁻¹) := by
    unfold etaSourceBox periodBox
    congr 1
    ext i
    fin_cases i <;> rfl
  have eT : etaBox K L η = periodBox 0 0 ((η * L * Real.sqrt K)⁻¹) := by
    unfold etaBox periodBox
    congr 1
    ext i
    fin_cases i <;> rfl
  unfold etaSourceMoment etaMoment
  rw [eS, eT, integral_periodBox K L q _ hq a]
  ring

/-- Li--Yang's actual two-period moment is now connected to the manuscript
moment, without any period-normalization assumption. -/
theorem etaSourceMoment_le_coneMoment {K L η q : ℝ}
    (hK : 0 < K) (hL : 0 < L) (hη : 0 < η) (hq : 0 ≤ q)
    (h : 1 ≤ η * K * L) (a : ℤ → ℤ → ℂ) :
    etaSourceMoment K L η q a ≤ (η * K * L) * coneMoment K L q a := by
  rw [etaSourceMoment_eq_etaMoment K L η q hq a]
  exact etaMoment_le hK hL hη hq h a

theorem etaSourceMoment_le_of_spacingParameters {D H N R Q η q : ℝ} {K L : ℕ}
    (p : SpacingParameters D H N R Q K L η) (hq : 0 ≤ q) (a : ℤ → ℤ → ℂ) :
    etaSourceMoment K L η q a ≤ (η * K * L) * coneMoment K L q a := by
  rw [etaSourceMoment_eq_etaMoment K L η q hq a]
  exact etaMoment_le_of_spacingParameters p hq a

end
end CircleDivisor.ExternalPeriodBridge
