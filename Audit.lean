import CircleDivisor
import Lean.Util.CollectAxioms

open Lean Elab Command

/-! Audit all exported CircleDivisor theorem declarations, including auxiliary theorems.
External inputs are theorem parameters. The September 8 main result and uniform
first-spacing estimate are proved in `EnergyV3` and explicitly audited below.
-/

run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut count := 0
  for (name, info) in env.constants.toList do
    if (`CircleDivisor).isPrefixOf name then
      if info matches .thmInfo _ then
        let axioms ← Lean.collectAxioms name
        for ax in axioms do
          unless allowed.contains ax do
            throwError "Unapproved axiom {ax} in {name}"
        count := count + 1
  logInfo m!"AUDIT_OK: {count} exported CircleDivisor theorems; axiom dependencies are contained in propext, Classical.choice, Quot.sound."
  logInfo "SCOPE: EnergyV3 main and uniform first-spacing theorems are conditional only on named external inputs. Legacy target statements are separate."

#print axioms CircleDivisor.Optimization.hard_interval_optimization
#print axioms CircleDivisor.Optimization.optimized_exponent_at_x0
#print axioms CircleDivisor.SpacingCount.lemma_3_2_real
#print axioms CircleDivisor.SpacingCount.lemma_3_2_uniform
#print axioms CircleDivisor.ScaleBounds.full_scale_bound_q
#print axioms CircleDivisor.AmplitudeIntegration.integral_norm_moment_two_cutoffs
#print axioms CircleDivisor.FourierEnergy.integral_weighted_fourth_moment_le_balanced_card
#print axioms CircleDivisor.Connections.spacing_count_from_divisor_input
#print axioms CircleDivisor.SchwartzCutoff.exists_cutoff
#print axioms CircleDivisor.AngularGrid.same_cell_of_safe_grid
#print axioms CircleDivisor.FourierLocalization.exists_scaled_energy_cutoff
#print axioms CircleDivisor.FourierLocalization.sharpProjection_modulated_sum
#print axioms CircleDivisor.firstSpacing_uniform_iff_pointwise
#print axioms CircleDivisor.BlockSeparation.caseB_uniform_margin
#print axioms CircleDivisor.BlockSeparation.actual_separation_of_power_margins
#print axioms CircleDivisor.ExternalInterfaces.etaMoment_le
#print axioms CircleDivisor.ExternalPeriodBridge.etaSourceMoment_eq_etaMoment
#print axioms CircleDivisor.DiscrepancyReduction.divisorError_sawtooth
#print axioms CircleDivisor.DiscrepancyReduction.circleError_sawtooth
#print axioms CircleDivisor.DiscrepancyReduction.beta_tail_bound
#print axioms CircleDivisor.FinalAssembly.main_of_sawtooth_bounds
#print axioms CircleDivisor.GuthMaldague.contributing_mass_threshold
#print axioms CircleDivisor.GuthMaldague.weightNormalization_pos
#print axioms CircleDivisor.ReciprocalPhase.reciprocal_phase_control
#print axioms CircleDivisor.LogScale.blockLengthB_eq_power
#print axioms CircleDivisor.LogScale.log_correction_eventually_small

#check CircleDivisor.MainTheoremStatement
#check CircleDivisor.FirstSpacingUniformStatement

#print axioms CircleDivisor.EnergyV3.uniformFirstSpacing_of_external_inputs
#print axioms CircleDivisor.EnergyV3.firstSpacing_of_external_inputs
#print axioms CircleDivisor.EnergyV3.main_of_external_inputs
#print axioms CircleDivisor.EnergyV3.circle_and_divisor_error
#check CircleDivisor.EnergyV3.main_of_external_inputs
#check CircleDivisor.EnergyV3.uniformFirstSpacing_of_external_inputs
#print axioms CircleDivisor.EnergyV3.Corollaries.sqrt_moment_of_external_inputs
#print axioms CircleDivisor.EnergyV3.Corollaries.nine_halves_moment_of_external_inputs
