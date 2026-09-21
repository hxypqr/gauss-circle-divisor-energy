-- EnergyV3 internal proof audit. External inputs are theorem parameters, not axioms.
-- Includes the complete actual-object assembly and final discrepancy theorem.
import CircleDivisor.EnergyV3.AdaptedMetric
import CircleDivisor.EnergyV3.AmplitudeConstants
import CircleDivisor.EnergyV3.AmplitudeCountable
import CircleDivisor.EnergyV3.AmplitudeScale
import CircleDivisor.EnergyV3.AnalyticAssembly
import CircleDivisor.EnergyV3.AngularAtoms
import CircleDivisor.EnergyV3.Arithmetic
import CircleDivisor.EnergyV3.ArithmeticInterface
import CircleDivisor.EnergyV3.ArithmeticMain
import CircleDivisor.EnergyV3.CanonicalLocalization
import CircleDivisor.EnergyV3.CapNesting
import CircleDivisor.EnergyV3.CaseAssembly
import CircleDivisor.EnergyV3.ClassDecomposition
import CircleDivisor.EnergyV3.CoarseDecomposition
import CircleDivisor.EnergyV3.CoarseEnergy
import CircleDivisor.EnergyV3.CoarseWindows
import CircleDivisor.EnergyV3.Construction
import CircleDivisor.EnergyV3.Corollaries
import CircleDivisor.EnergyV3.CountableAveraging
import CircleDivisor.EnergyV3.CrudeEnergy
import CircleDivisor.EnergyV3.DensitySums
import CircleDivisor.EnergyV3.DensityTransfer
import CircleDivisor.EnergyV3.ElementaryReciprocal
import CircleDivisor.EnergyV3.EndpointTransfer
import CircleDivisor.EnergyV3.EnvelopeEnergies
import CircleDivisor.EnergyV3.ExternalArithmetic
import CircleDivisor.EnergyV3.FirstMass
import CircleDivisor.EnergyV3.FirstSpacingAssembly
import CircleDivisor.EnergyV3.FirstSpacingTransfer
import CircleDivisor.EnergyV3.FirstSpacingProof
import CircleDivisor.EnergyV3.FourierTransport
import CircleDivisor.EnergyV3.HardReciprocal
import CircleDivisor.EnergyV3.KernelActual
import CircleDivisor.EnergyV3.KernelBounds
import CircleDivisor.EnergyV3.KernelDensity
import CircleDivisor.EnergyV3.KernelDerivatives
import CircleDivisor.EnergyV3.KernelEnvelope
import CircleDivisor.EnergyV3.LinearTransport
import CircleDivisor.EnergyV3.LocalDensityActual
import CircleDivisor.EnergyV3.Main
import CircleDivisor.EnergyV3.LocalizationNormalization
import CircleDivisor.EnergyV3.MetricTransport
import CircleDivisor.EnergyV3.NeighborCount
import CircleDivisor.EnergyV3.Optimization
import CircleDivisor.EnergyV3.PairedCount
import CircleDivisor.EnergyV3.PairedCountReal
import CircleDivisor.EnergyV3.PairEnergies
import CircleDivisor.EnergyV3.QuadraticDecomposition
import CircleDivisor.EnergyV3.ReciprocalConclusion
import CircleDivisor.EnergyV3.RectangleWeights
import CircleDivisor.EnergyV3.ReductionAbel
import CircleDivisor.EnergyV3.ReductionDyadic
import CircleDivisor.EnergyV3.ReductionFourier
import CircleDivisor.EnergyV3.ReductionMain
import CircleDivisor.EnergyV3.ReductionPower
import CircleDivisor.EnergyV3.ReductionReciprocal
import CircleDivisor.EnergyV3.ReductionWeight
import CircleDivisor.EnergyV3.RefinedEnergy
import CircleDivisor.EnergyV3.RotationJacobian
import CircleDivisor.EnergyV3.SameRayCount
import CircleDivisor.EnergyV3.SameRayEnergies
import CircleDivisor.EnergyV3.ScaleBounds
import CircleDivisor.EnergyV3.ScaleExponents
import CircleDivisor.EnergyV3.ShellSummation
import CircleDivisor.EnergyV3.SpacingTransfer
import CircleDivisor.EnergyV3.Statements
import CircleDivisor.EnergyV3.TorusAtoms
import CircleDivisor.EnergyV3.TorusProjection
import CircleDivisor.EnergyV3.TwoClassLocalization
import CircleDivisor.EnergyV3.UniformFirstSpacingTransfer
import CircleDivisor.EnergyV3.WeightGeometry
import CircleDivisor.EnergyV3.WeightMass
import CircleDivisor.EnergyV3.WeightOverlap

-- AdaptedMetric
#print axioms CircleDivisor.EnergyV3.AdaptedMetric.adapted_inverse_coordinates
#print axioms CircleDivisor.EnergyV3.AdaptedMetric.transpose_controls_adapted
-- AmplitudeConstants
#print axioms CircleDivisor.EnergyV3.AmplitudeConstants.norm_add_rpow_le
#print axioms CircleDivisor.EnergyV3.AmplitudeConstants.moment_add
-- AmplitudeCountable
#print axioms CircleDivisor.EnergyV3.AmplitudeCountable.gm_truncated_distribution
#print axioms CircleDivisor.EnergyV3.AmplitudeCountable.moment_of_gm
-- AmplitudeScale
#print axioms CircleDivisor.EnergyV3.AmplitudeScale.scale_term
#print axioms CircleDivisor.EnergyV3.AmplitudeScale.scale_sum
-- AngularAtoms
#print axioms CircleDivisor.EnergyV3.AngularAtoms.generator_rotated_angle
#print axioms CircleDivisor.EnergyV3.AngularAtoms.same_cap_index_diameter
-- Arithmetic
#print axioms CircleDivisor.EnergyV3.Arithmetic.four_reference_endpoint_bounds
#print axioms CircleDivisor.EnergyV3.Arithmetic.four_actual_endpoint_bounds
-- ArithmeticInterface
#print axioms CircleDivisor.EnergyV3.ArithmeticInterface.spacing_scale_bounds
#print axioms CircleDivisor.EnergyV3.ArithmeticInterface.spacingMajorized_of_firstSpacing
-- ArithmeticMain
#print axioms CircleDivisor.EnergyV3.main_of_firstSpacing
-- CanonicalLocalization
#print axioms CircleDivisor.EnergyV3.CanonicalLocalization.localizedSchwartz_tsupport
#print axioms CircleDivisor.EnergyV3.CanonicalLocalization.classPoints_partition
-- CapNesting
#print axioms CircleDivisor.EnergyV3.CapNesting.coarsePoints_disjoint
#print axioms CircleDivisor.EnergyV3.CapNesting.coarsePoints_union
-- CaseAssembly
#print axioms CircleDivisor.EnergyV3.CaseAssembly.selected_case
#print axioms CircleDivisor.EnergyV3.CaseAssembly.eventually_log_correction
-- ClassDecomposition
#print axioms CircleDivisor.EnergyV3.ClassDecomposition.jacobian_rotation
#print axioms CircleDivisor.EnergyV3.ClassDecomposition.jacobian_rotatedPhysical
-- CoarseDecomposition
#print axioms CircleDivisor.EnergyV3.CoarseDecomposition.average_pairSum_split
#print axioms CircleDivisor.EnergyV3.CoarseDecomposition.localMass_sub_sameMass
-- CoarseWindows
#print axioms CircleDivisor.EnergyV3.CoarseWindows.sameWindow
#print axioms CircleDivisor.EnergyV3.CoarseWindows.crossWindow
-- Construction
#print axioms CircleDivisor.EnergyV3.Construction.extra_standing_of_margins
#print axioms CircleDivisor.EnergyV3.Construction.extra_standing_threshold
-- CountableAveraging
#print axioms CircleDivisor.EnergyV3.CountableAveraging.finite_averaging
#print axioms CircleDivisor.EnergyV3.CountableAveraging.countable_averaging
-- CrudeEnergy
#print axioms CircleDivisor.EnergyV3.CrudeEnergy.actual_crude_energies
#print axioms CircleDivisor.EnergyV3.CrudeEnergy.actual_profile_crude
-- DensitySums
#print axioms CircleDivisor.EnergyV3.DensitySums.relation_decay_sum
#print axioms CircleDivisor.EnergyV3.DensitySums.same_relation_decay_sum
-- ElementaryReciprocal
#print axioms CircleDivisor.EnergyV3.ElementaryReciprocal.elementary_double_sum
#print axioms CircleDivisor.EnergyV3.ElementaryReciprocal.reciprocalSum_trivial
-- EndpointTransfer
#print axioms CircleDivisor.EnergyV3.EndpointTransfer.four_coefficient_ranges
#print axioms CircleDivisor.EnergyV3.EndpointTransfer.actual_sieveMonomial_bound
-- EnvelopeEnergies
#print axioms CircleDivisor.EnergyV3.EnvelopeEnergies.finite_first_mass
#print axioms CircleDivisor.EnergyV3.EnvelopeEnergies.countable_first_mass
-- FirstMass
#print axioms CircleDivisor.EnergyV3.FirstMass.envelope_grouped_average
#print axioms CircleDivisor.EnergyV3.FirstMass.envelope_grouped_average_nonneg
-- FirstSpacingAssembly
#print axioms CircleDivisor.EnergyV3.FirstSpacingAssembly.coefficient_bound
#print axioms CircleDivisor.EnergyV3.FirstSpacingAssembly.moment_bound
-- FirstSpacingTransfer
#print axioms CircleDivisor.EnergyV3.FirstSpacingTransfer.fourTerm_one_le
#print axioms CircleDivisor.EnergyV3.FirstSpacingTransfer.firstSpacing_of_large_localized
-- FourierTransport
#print axioms CircleDivisor.EnergyV3.FourierTransport.support_rotated_cutoff
#print axioms CircleDivisor.EnergyV3.FourierTransport.integral_rotatedPhysical
-- HardReciprocal
#print axioms CircleDivisor.EnergyV3.HardReciprocal.hard_reciprocal_fixed_moment
#print axioms CircleDivisor.EnergyV3.HardReciprocal.hard_reciprocal_uniform
-- KernelActual
#print axioms CircleDivisor.EnergyV3.KernelActual.physical_kernel_decay
#print axioms CircleDivisor.EnergyV3.KernelActual.transported_physical_kernel_decay
-- KernelBounds
#print axioms CircleDivisor.EnergyV3.KernelBounds.actual_normalized_kernel_decay
#print axioms CircleDivisor.EnergyV3.KernelBounds.actual_scaled_kernel_decay
-- KernelDensity
#print axioms CircleDivisor.EnergyV3.KernelDensity.decay_comparison
#print axioms CircleDivisor.EnergyV3.KernelDensity.uniform_transported_average
-- KernelDerivatives
#print axioms CircleDivisor.EnergyV3.KernelDerivatives.baseWeight_complex_smooth
#print axioms CircleDivisor.EnergyV3.KernelDerivatives.baseWeight_derivative_bound
-- KernelEnvelope
#print axioms CircleDivisor.EnergyV3.KernelEnvelope.transportedEnvelopeKernel_eq
#print axioms CircleDivisor.EnergyV3.KernelEnvelope.transported_envelope_kernel_decay
-- LinearTransport
#print axioms CircleDivisor.EnergyV3.LinearTransport.pair_energy_comp
#print axioms CircleDivisor.EnergyV3.LinearTransport.moment_comp
-- LocalizationNormalization
#print axioms CircleDivisor.EnergyV3.LocalizationNormalization.coneMoment_le_localized_integral
#print axioms CircleDivisor.EnergyV3.LocalizationNormalization.coneFrequency_eq_frequency
-- MetricTransport
#print axioms CircleDivisor.EnergyV3.MetricTransport.canonical_decay_comparison
#print axioms CircleDivisor.EnergyV3.MetricTransport.transported_kernel_arithmetic_decay
-- NeighborCount
#print axioms CircleDivisor.EnergyV3.NeighborCount.actual_dual_neighbor_count
#print axioms CircleDivisor.EnergyV3.NeighborCount.shell_series_bound
-- Optimization
#print axioms CircleDivisor.EnergyV3.rational_certificate
#print axioms CircleDivisor.EnergyV3.left_exponent_strict
-- PairedCount
#print axioms CircleDivisor.EnergyV3.PairedCount.Admissible.bounded
#print axioms CircleDivisor.EnergyV3.PairedCount.count_quadruples
-- PairedCountReal
#print axioms CircleDivisor.EnergyV3.PairedCount.count_real_parameters
#print axioms CircleDivisor.EnergyV3.PairedCount.paired_count_real
-- PairEnergies
#print axioms CircleDivisor.EnergyV3.PairEnergies.balanced_cross_count_family
#print axioms CircleDivisor.EnergyV3.PairEnergies.torus_cross_energy_family
-- QuadraticDecomposition
#print axioms CircleDivisor.EnergyV3.QuadraticDecomposition.grouped_pairSum_real_nonneg
#print axioms CircleDivisor.EnergyV3.QuadraticDecomposition.pairSum_split
-- ReciprocalConclusion
#print axioms CircleDivisor.EnergyV3.ReciprocalConclusion.weighted_reciprocal_of_inputs
#print axioms CircleDivisor.EnergyV3.ReciprocalConclusion.reciprocalRectangles_of_inputs
-- RectangleWeights
#print axioms CircleDivisor.EnergyV3.sum_dyadic_upperCutoff
#print axioms CircleDivisor.EnergyV3.reciprocalSum_upperCutoffs
-- ReductionAbel
#print axioms CircleDivisor.EnergyV3.fejer_sum_eq_re
#print axioms CircleDivisor.EnergyV3.sawtooth_sum_le_fourier
-- ReductionDyadic
#print axioms CircleDivisor.EnergyV3.sum_dyadic_starts
#print axioms CircleDivisor.EnergyV3.sum_dyadic_starts_le
-- ReductionFourier
#print axioms CircleDivisor.EnergyV3.dyadicBlock_length
#print axioms CircleDivisor.EnergyV3.finite_fourier_reduction
-- ReductionMain
#print axioms CircleDivisor.EnergyV3.main_of_fullReciprocalSawtooth
#print axioms CircleDivisor.EnergyV3.main_of_reciprocal_rectangles
-- ReductionPower
#print axioms CircleDivisor.EnergyV3.sawtooth_trivial_bound
#print axioms CircleDivisor.EnergyV3.rectangle_to_sawtooth_power
-- ReductionReciprocal
#print axioms CircleDivisor.EnergyV3.dyadicReciprocalSawtooth_of_rectangles
#print axioms CircleDivisor.EnergyV3.fullReciprocalSawtooth_of_dyadic
-- ReductionWeight
#print axioms CircleDivisor.EnergyV3.vaaler_coefficient_abelCost
#print axioms CircleDivisor.EnergyV3.fejer_coefficient_abelCost
-- RefinedEnergy
#print axioms CircleDivisor.EnergyV3.RefinedEnergy.cross_familyEnergy
#print axioms CircleDivisor.EnergyV3.RefinedEnergy.familyEnergy_ofReal
-- RotationJacobian
#print axioms CircleDivisor.EnergyV3.RotationJacobian.rotatedPhysical_jacobian
-- SameRayCount
#print axioms CircleDivisor.EnergyV3.SameRayCount.RealAdmissible.ceiling
#print axioms CircleDivisor.EnergyV3.SameRayCount.count_real
-- SameRayEnergies
#print axioms CircleDivisor.EnergyV3.PairEnergies.localized_same_energy_family
#print axioms CircleDivisor.EnergyV3.PairEnergies.localized_cross_energy_family
-- ScaleBounds
#print axioms CircleDivisor.EnergyV3.ScaleBounds.full_scale_bound
#print axioms CircleDivisor.EnergyV3.ScaleBounds.full_scale_bound_q
-- ScaleExponents
#print axioms CircleDivisor.EnergyV3.ScaleExponents.cross_ray_small
#print axioms CircleDivisor.EnergyV3.ScaleExponents.cross_ray_bound
-- ShellSummation
#print axioms CircleDivisor.EnergyV3.ShellSummation.decay_le_shell
#print axioms CircleDivisor.EnergyV3.ShellSummation.finite_decay_sum
-- SpacingTransfer
#print axioms CircleDivisor.EnergyV3.SpacingTransfer.moment_contribution_bound
#print axioms CircleDivisor.EnergyV3.SpacingTransfer.actual_moment_contribution_bound
-- TorusAtoms
#print axioms CircleDivisor.EnergyV3.PairEnergies.phasedCoefficient_norm
#print axioms CircleDivisor.EnergyV3.PairEnergies.phased_mass
-- TorusProjection
#print axioms CircleDivisor.EnergyV3.TorusProjection.fiberCoefficient_norm_le_card
#print axioms CircleDivisor.EnergyV3.TorusProjection.weighted_projection_le_fiber_energy
-- TwoClassLocalization
#print axioms CircleDivisor.EnergyV3.TwoClassLocalization.localized_moment_le_two_classes
#print axioms CircleDivisor.EnergyV3.TwoClassLocalization.localized_moment_le_uniform_classes
-- WeightGeometry
#print axioms CircleDivisor.EnergyV3.WeightGeometry.coordinateEquiv_symm_norm_le
#print axioms CircleDivisor.EnergyV3.WeightGeometry.canonical_synthesis_norm_le
-- WeightMass
#print axioms CircleDivisor.EnergyV3.WeightMass.envelopeWeight_mass
#print axioms CircleDivisor.EnergyV3.WeightMass.actual_countable_averaging
-- WeightOverlap
#print axioms CircleDivisor.EnergyV3.WeightOverlap.actual_envelope_finite_overlap
#print axioms CircleDivisor.EnergyV3.WeightOverlap.actual_envelope_overlap
#print axioms CircleDivisor.EnergyV3.PairedCount.count_nonzero
#print axioms CircleDivisor.EnergyV3.PairedCount.count_zero_rectangle
#print axioms CircleDivisor.EnergyV3.TorusProjection.weighted_projection_identity
#print axioms CircleDivisor.EnergyV3.AngularAtoms.whole_ray_atoms_one_cap
#print axioms CircleDivisor.EnergyV3.CanonicalLocalization.exists_actual_canonical_projections
#print axioms CircleDivisor.EnergyV3.CountableAveraging.countable_averaging
#print axioms CircleDivisor.EnergyV3.FirstMass.sum_square_integral
#print axioms CircleDivisor.EnergyV3.LiYangInput
#print axioms CircleDivisor.GuthMaldague.GuthMaldagueInput
-- Actual analytic assembly, after all local objects have been instantiated.
#print axioms CircleDivisor.EnergyV3.CoarseEnergy.first_masses
#print axioms CircleDivisor.EnergyV3.CoarseEnergy.profile_energies
#print axioms CircleDivisor.EnergyV3.CoarseEnergy.energyConstant_rotatedPhysical
#print axioms CircleDivisor.EnergyV3.LocalDensityActual.actual_average_decay
#print axioms CircleDivisor.EnergyV3.LocalDensityActual.actual_local_density
#print axioms CircleDivisor.EnergyV3.DensityTransfer.actual_mass_densities
#print axioms CircleDivisor.EnergyV3.AnalyticAssembly.uniform_class_moment_explicit_q
#print axioms CircleDivisor.EnergyV3.UniformFirstSpacingTransfer.uniformFirstSpacing_of_large_localized
#print axioms CircleDivisor.EnergyV3.firstSpacing_of_uniform
-- Final conclusions: only the explicitly declared source inputs remain.
#print axioms CircleDivisor.EnergyV3.uniformFirstSpacing_of_external_inputs
#print axioms CircleDivisor.EnergyV3.firstSpacing_of_external_inputs
#print axioms CircleDivisor.EnergyV3.main_of_external_inputs
#print axioms CircleDivisor.EnergyV3.circle_and_divisor_error
#print axioms CircleDivisor.EnergyV3.Corollaries.sqrt_moment_of_uniform
#print axioms CircleDivisor.EnergyV3.Corollaries.sqrt_moment_of_external_inputs
#print axioms CircleDivisor.EnergyV3.Corollaries.nine_halves_conditions
#print axioms CircleDivisor.EnergyV3.Corollaries.nine_halves_moment_of_external_inputs
