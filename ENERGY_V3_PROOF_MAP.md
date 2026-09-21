# 新稿内部证明与 Lean 定理对应表

本文对应 [2026 年 9 月 8 日稿件](manuscript/Gauss_circle_divisor_energy.tex)。新版指数是
`573 / 1828 = 0.3134573304157549234…`；旧聊天中的 `0.3134615421…` 不是这版的目标。
已核对工作区稿件与用户提供的 TeX 附件 SHA-256 相同。
实际目标定义在 [Statements.lean](CircleDivisor/EnergyV3/Statements.lean)，继续使用原项目中实际的圆内整点计数、除数和、误差函数及有限指数和。

## 当前状态与阅读方法

内部主证明链已经连接完成：[FirstSpacingProof.lean](CircleDivisor/EnergyV3/FirstSpacingProof.lean)
的 `uniformFirstSpacing_of_external_inputs` 从 GM 与经典除数界推出稿件的统一第一间距定理，
`firstSpacing_of_external_inputs` 导出固定矩版本；
[Main.lean](CircleDivisor/EnergyV3/Main.lean) 的 `main_of_external_inputs` 再连接全部算术与误差归约。
`circle_and_divisor_error` 直接写出实际圆问题和除数问题误差的 `573/1828 + ε` 界。
**最终结论仅保留本文末尾明确列出的外部定理参数，不再接受第一间距、局部密度、四次能量或最终误差归约作为内部待证前提。**

以下名称一般省略前缀 `CircleDivisor.EnergyV3`。例如
`PairedCount.paired_count_real` 指该前缀下的定理。
文件名不是命名空间的可靠推断方式：`Optimization`、`Reduction*`、`ArithmeticMain` 等文件的若干结论直接位于 `EnergyV3` 命名空间。
链接指向实际文件；本表列出的是已写成证明的内部结果，而不是仅定义为 `Prop` 的目标。

## §2：两尺度整数计数与实际四次能量

| 稿件内容 | 证明文件与主要定理 | 已证明的具体内容 |
| --- | --- | --- |
| 母线差分、因子分解、非零分支与零矩形分支 | [PairedCount](CircleDivisor/EnergyV3/PairedCount.lean)：`count_nonzero`、`count_zero_rectangle`、`count_quadruples` | 真实整数坐标、重构和单射；两分支分别计数，保留配对宽度 `W` 与基点宽度 `V`。 |
| 实数窗口到整数计数 | [PairedCountReal](CircleDivisor/EnergyV3/PairedCountReal.lean)：`PairedCount.paired_count_real` | 天花板取整和常数全部处理，推出 `K (W²L² + VWL) (KL)^ε` 型界。经典除数界作为明确参数。 |
| 加权投影原理 | [TorusProjection](CircleDivisor/EnergyV3/TorusProjection.lean)：`weighted_projection_identity`、`weighted_projection_le_fiber_energy` | 对实际二维环面 Haar 积分证明复系数投影恒等式，再用频率纤维计数控制能量。 |
| 不同母线的有限窗口能量 | [PairEnergies](CircleDivisor/EnergyV3/PairEnergies.lean)：`balanced_cross_count_family`、`torus_cross_energy_family` | 实际 pair relation、投影频率 `(l,kl)`、有限复系数和；对不交窗口族直接计数，没有逐窗口求和造成的额外 `K/V` 损失。 |
| 同母线能量 | [SameRayCount](CircleDivisor/EnergyV3/SameRayCount.lean)：`count_real`；[SameRayEnergies](CircleDivisor/EnergyV3/SameRayEnergies.lean)：`PairEnergies.localized_same_energy_family` | 同母线四元组的 `KVL² + KL³` 界及实际三维局部化能量。 |
| 第三个物理变量与实际局部化 | [TorusAtoms](CircleDivisor/EnergyV3/TorusAtoms.lean)：`PairEnergies.phased_mass`；[SameRayEnergies](CircleDivisor/EnergyV3/SameRayEnergies.lean)：`PairEnergies.localized_cross_energy_family` | 第三个坐标只改变模长一的系数；通过原项目已证明的 [FourierLocalization](CircleDivisor/FourierLocalization.lean) 转入真实 Schwartz 截断的三维积分。没有把近似频率关系宣布为精确整数关系。 |

## §3 与附录 A：局部化、规范角帽和真实局部平均

| 稿件内容 | 证明文件与主要定理 | 已证明的具体内容 |
| --- | --- | --- |
| A.1 原始矩到全空间局部化矩 | [LocalizationNormalization](CircleDivisor/EnergyV3/LocalizationNormalization.lean)：`coneMoment_le_localized_integral`、`localized_integrable_norm_rpow` | 实际周期重复、线性变量替换、Jacobian 和积分区域均已处理；得到 `16/P³` 乘实际全空间矩的上界。 |
| 固定圆锥映射、旋转和 Fourier 变换 | [LinearTransport](CircleDivisor/EnergyV3/LinearTransport.lean)：`integral_comp`、`memLp_comp`；[FourierTransport](CircleDivisor/EnergyV3/FourierTransport.lean)：`fourier_comp`、`rotatedPhysical_pairing` | 真实连续线性等价及转置关系；Fourier 支撑和 Lebesgue 积分的变换，而非自由指定一个 Jacobian。 |
| A.2 两网格与整个 Fourier 原子 | [AngularAtoms](CircleDivisor/EnergyV3/AngularAtoms.lean)：`whole_ray_atoms_one_cap`、`exists_ray_assignment`、`small_atom_conditions` | 显式角度扰动与两次旋转避开网格边界；同一母线的整片闭原子选入同一个实际规范帽，选择不依赖径向变量。 |
| 真正的 Schwartz 函数、锐投影与闭支撑 | [CanonicalLocalization](CircleDivisor/EnergyV3/CanonicalLocalization.lean)：`localizedSchwartz_coe`、`exists_actual_canonical_projections`、`localizedSchwartz_tsupport` | 构造实际 Schwartz 有限和；实际 `capFunction` 等于指定原子子和；证明 `tsupport` 的圆锥邻域包含，保留闭支撑所需的严格余量。 |
| 两类函数精确分解与合并 | [ClassDecomposition](CircleDivisor/EnergyV3/ClassDecomposition.lean)：`original_two_classes`、`class_moment_transport`、`jacobian_rotatedPhysical`；[TwoClassLocalization](CircleDivisor/EnergyV3/TwoClassLocalization.lean)：`localized_moment_le_uniform_classes` | 两类子和相加恰好是原函数；旋转的 Jacobian 为一；实际全空间矩由两类矩控制，常数不依赖所选旋转。 |
| 细帽到粗帽的真实嵌套和分割 | [CapNesting](CircleDivisor/EnergyV3/CapNesting.lean)：`exists_fineChild_parent`、`fineChild_parent_unique`、`coarsePoints_disjoint`、`coarsePoints_union` | `fineChildren` 的存在性、在非空细帽上的唯一性、实际点集的不交并。 |
| 粗帽与细帽对应的两个整数窗口 | [AngularAtoms](CircleDivisor/EnergyV3/AngularAtoms.lean)：`same_cap_index_diameter`；[CoarseWindows](CircleDivisor/EnergyV3/CoarseWindows.lean)：`sameWindow`、`crossWindow` | 由实际帽成员关系证明 `k` 直径界，分别产生细尺度配对宽度和粗尺度基点宽度。 |
| A.3 具体权重的质量和有限重叠 | [WeightGeometry](CircleDivisor/EnergyV3/WeightGeometry.lean)、[WeightOverlap](CircleDivisor/EnergyV3/WeightOverlap.lean)：`actual_envelope_overlap`；[WeightMass](CircleDivisor/EnergyV3/WeightMass.lean)：`envelopeWeight_mass` | 对实际包络矩阵、整数格平移与 product-tail 权重证明体积/质量公式和全格点有界重叠。 |
| A.6 可数平均 | [CountableAveraging](CircleDivisor/EnergyV3/CountableAveraging.lean)：`countable_averaging`；[WeightMass](CircleDivisor/EnergyV3/WeightMass.lean)：`actual_countable_averaging` | 从实际质量和重叠证明加权可积性、Cauchy 不等式、能量级数可和性及其上界；没有把目标平均估计作为输入。 |
| A.4 适配 Fourier 度量 | [AdaptedMetric](CircleDivisor/EnergyV3/AdaptedMetric.lean)：`transpose_controls_adapted`；[MetricTransport](CircleDivisor/EnergyV3/MetricTransport.lean)：`transported_kernel_arithmetic_decay` | 对实际转置矩阵逐坐标计算，并比较圆锥规范帽的真实包络度量与整数计数使用的度量。 |
| A.4 核的快速衰减 | [KernelDerivatives](CircleDivisor/EnergyV3/KernelDerivatives.lean)：`baseWeight_derivative_bound`；[KernelBounds](CircleDivisor/EnergyV3/KernelBounds.lean)：`actual_normalized_kernel_decay`、`actual_scaled_kernel_decay`；[KernelActual](CircleDivisor/EnergyV3/KernelActual.lean)、[KernelEnvelope](CircleDivisor/EnergyV3/KernelEnvelope.lean) | 对实际平方截断乘具体权重证明任意阶 Fourier 衰减；常数先于中心、尺度和有界畸变线性映射量化，不残留导数界假设。 |
| A.5 邻居计数与衰减求和 | [NeighborCount](CircleDivisor/EnergyV3/NeighborCount.lean)：`actual_dual_neighbor_count`；[ShellSummation](CircleDivisor/EnergyV3/ShellSummation.lean)：`finite_decay_sum`；[DensitySums](CircleDivisor/EnergyV3/DensitySums.lean)：`relation_decay_sum`、`same_relation_decay_sum` | 从实际频率差推出整数矩形计数，再作 dyadic 壳求和；同母线关系有更强界。 |
| 真实局部密度的最后连接 | [LocalDensityActual](CircleDivisor/EnergyV3/LocalDensityActual.lean)：`actual_cap_center`、`actual_average_decay`、`actual_local_density` | 从非空实际粗帽选择中心，再把核衰减、转置度量和邻居计数连接成两个实际平均的密度界。该模块已独立编译通过。 |
| 一次质量、同母线非负性与精确分解 | [FirstMass](CircleDivisor/EnergyV3/FirstMass.lean)：`sum_square_integral`、`envelope_grouped_average_nonneg`；[QuadraticDecomposition](CircleDivisor/EnergyV3/QuadraticDecomposition.lean)；[CoarseDecomposition](CircleDivisor/EnergyV3/CoarseDecomposition.lean)：`localMass_sub_sameMass` | 实际有限和对角正交、按母线分组的平方和与真实平均的 `M = D + C`。 |
| 三维能量到包络能量 | [EnvelopeEnergies](CircleDivisor/EnergyV3/EnvelopeEnergies.lean)：`transported_family_average_energy`、`countable_first_mass`；[RefinedEnergy](CircleDivisor/EnergyV3/RefinedEnergy.lean)：`same_familyEnergy`、`cross_familyEnergy`；[CrudeEnergy](CircleDivisor/EnergyV3/CrudeEnergy.lean)：`actual_profile_crude`；[CoarseEnergy](CircleDivisor/EnergyV3/CoarseEnergy.lean)：`profile_energies` | 真实变量变换、`MemLp 2`、可数包络求和、精细计数与粗界共同给出两个 `min` 能量型。 |

这条应用链通过已证明的 Fourier 支撑正交转移实现稿件的局部化功能。
它不需要先另建一个适用于任意周期函数的全面周期化库；实际应用的积分不等式已经在上述定理中证明。

## §4：限制幅度、分尺度估计与第一间距

| 稿件内容 | 证明文件与主要定理 | 已证明的具体内容 |
| --- | --- | --- |
| 真正可数包络的幅度分裂 | [AmplitudeCountable](CircleDivisor/EnergyV3/AmplitudeCountable.lean)：`gm_scale_split`、`gm_truncated_distribution`、`moment_of_gm` | 对实际 GM 非负可数和作分裂和层蛋糕积分；可测性、可和性及积分交换均处理。 |
| 同母线与不同母线各尺度优化 | [ScaleExponents](CircleDivisor/EnergyV3/ScaleExponents.lean)：`cross_ray_bound`；[ScaleBounds](CircleDivisor/EnergyV3/ScaleBounds.lean)：`full_scale_bound_q`；[AmplitudeScale](CircleDivisor/EnergyV3/AmplitudeScale.lean)：`scale_term`、`scale_sum` | 对真实实数幂证明四项界，覆盖最小尺度与中间尺度，第三项为新版 `K^(q−2) L^(q−3)`。 |
| 幅度积分与 dyadic 尺度合并 | [FirstSpacingAssembly](CircleDivisor/EnergyV3/FirstSpacingAssembly.lean)：`coefficient_bound`、`moment_bound` | 振幅积分中的 `q/(q−4)` 及尺度数损失已有明确公式；该通用总装仍需实际局部数据实例化。 |
| 有界 `KL` 与原始积分归约 | [FirstSpacingTransfer](CircleDivisor/EnergyV3/FirstSpacingTransfer.lean)：`coneMoment_trivial`、`firstSpacing_of_large_localized`；[AmplitudeConstants](CircleDivisor/EnergyV3/AmplitudeConstants.lean) | 有界参数用实际有限和初等界处理；大参数选取 `P ≤ R < 4P`、合并两类矩并回到原始 `coneMoment`。 |
| 第一间距的最终实际对象装配 | [DensityTransfer](CircleDivisor/EnergyV3/DensityTransfer.lean)：`actual_mass_densities`；[AnalyticAssembly](CircleDivisor/EnergyV3/AnalyticAssembly.lean)：`uniform_class_moment_explicit_q`；[UniformFirstSpacingTransfer](CircleDivisor/EnergyV3/UniformFirstSpacingTransfer.lean)：`uniformFirstSpacing_of_large_localized`；[FirstSpacingProof](CircleDivisor/EnergyV3/FirstSpacingProof.lean)：`uniformFirstSpacing_of_external_inputs` | 实际局部对象和两类函数全部实例化；常数先于 `q` 量化，只留下 `q/(q−4)` 的显式依赖。 |
| 平方根推论和新版端点区间 | [Corollaries](CircleDivisor/EnergyV3/Corollaries.lean)：`sqrt_moment_of_uniform`、`sqrt_moment_of_external_inputs`、`nine_halves_conditions`、`nine_halves_moment_of_external_inputs` | 两个幂条件下的平方根型矩界，保留统一 `q` 常数；`q=9/2` 时实际区间为 `L^(11/7) ≤ K ≤ L³`。 |

**统一量词已保留。** `UniformFirstSpacingStatement` 的顺序是
`∀ ε > 0, ∃ C > 0, ∀ q ∈ (4,9/2], …`，右侧显式出现 `q/(q−4)`，
与稿件 Theorem 1.2 的常数独立性相符。
`uniformFirstSpacing_of_external_inputs` 证明这个较强结论，`firstSpacing_of_uniform` 导出固定矩接口供 §6 使用。

## §5–6 与附录 B/C：算术输入、块尺度和有理优化

| 稿件内容 | 证明文件与主要定理 | 已证明的具体内容 |
| --- | --- | --- |
| 初等区间和有限参数范围 | [ElementaryReciprocal](CircleDivisor/EnergyV3/ElementaryReciprocal.lean)：`elementary_double_sum`、`reciprocalSum_trivial` | 从单变量经典估计导出二维 reciprocal sum 的初等范围；有限参数部分亦由实际和控制。 |
| 候选块、额外 standing conditions | [Construction](CircleDivisor/EnergyV3/Construction.lean)：`extra_standing_of_margins`、`extra_standing_threshold`；[CaseAssembly](CircleDivisor/EnergyV3/CaseAssembly.lean)：`selected_case`、`eventually_log_correction` | Case A/B、整数块长可比、对数修正及六个调用尺度条件的内部验证。 |
| 附录 C 的辅助尺度 | [Construction](CircleDivisor/EnergyV3/Construction.lean)：`caseA_subsidiary_identities`、`shortening_subsidiary_ratio`、`caseA_subsidiary_ratios`、`caseB_v₂_margin` | `V₀,V₁,V₂` 的精确指数恒等式和 `60/17` 缩短效应；严格区分源引理内部构造与应用假设。 |
| 实际 first-spacing 矩进入大筛接口 | [SpacingTransfer](CircleDivisor/EnergyV3/SpacingTransfer.lean)：`actual_moment_contribution_bound`；[ArithmeticInterface](CircleDivisor/EnergyV3/ArithmeticInterface.lean)：`spacingMajorized_of_firstSpacing` | 实际有限源矩与本稿 `coneMoment` 之间的归一化、系数一致性和尺度界。 |
| 分母幂、块长幂和四个端点 | [Arithmetic](CircleDivisor/EnergyV3/Arithmetic.lean)：`denominator_powers`、`block_powers`、`four_reference_endpoint_bounds`、`four_actual_endpoint_bounds`；[EndpointTransfer](CircleDivisor/EnergyV3/EndpointTransfer.lean)：`actual_sieveMonomial_bound` | 新四项公式代入源端点，所有实数幂、可比常数和端点单调性均实际证明。 |
| 全困难区间的精确有理优化 | [Optimization](CircleDivisor/EnergyV3/Optimization.lean)：`four_moment_optimization`、`rational_certificate`、`left_exponent_strict` | 精确有理数证明 `θ=573/1828`；四个固定矩为 `201/50,17/4,22/5,9/2`，避免要求外部 Li–Yang 常数对连续 `q` 一致。 |
| 困难区间统一常数和矩形估计 | [HardReciprocal](CircleDivisor/EnergyV3/HardReciprocal.lean)：`hard_reciprocal_fixed_moment`、`hard_reciprocal_uniform`；[ReciprocalConclusion](CircleDivisor/EnergyV3/ReciprocalConclusion.lean)：`weighted_reciprocal_of_inputs`、`reciprocalRectangles_of_inputs` | 对实际 BV 加权指数和合并初等/困难区间、四矩常数、有限参数阈值及任意上截断矩形。 |

## §7：有限 Fourier 归约到两个误差函数

| 稿件内容 | 证明文件与主要定理 | 已证明的具体内容 |
| --- | --- | --- |
| Vaaler/Fejér 系数及 Abel 代价 | [ReductionWeight](CircleDivisor/EnergyV3/ReductionWeight.lean)：`vaaler_coefficient_abelCost`、`fejer_coefficient_abelCost`；[ReductionAbel](CircleDivisor/EnergyV3/ReductionAbel.lean)：`sawtooth_sum_le_fourier` | 实际有限 Fourier 多项式、系数变差和加权部分求和。Vaaler 近似本身是明确经典输入。 |
| dyadic 分割与任意截断 | [ReductionDyadic](CircleDivisor/EnergyV3/ReductionDyadic.lean)：`sum_dyadic_starts_le`；[ReductionFourier](CircleDivisor/EnergyV3/ReductionFourier.lean)：`finite_fourier_reduction`；[RectangleWeights](CircleDivisor/EnergyV3/RectangleWeights.lean)：`reciprocalSum_upperCutoffs` | 有限索引区间的实际分割，严格处理上截断而非只证明完整 dyadic 区间。 |
| 最终误差幂的连接 | [ReductionPower](CircleDivisor/EnergyV3/ReductionPower.lean)：`rectangle_to_sawtooth_power`；[ReductionReciprocal](CircleDivisor/EnergyV3/ReductionReciprocal.lean)：`dyadicReciprocalSawtooth_of_rectangles`、`fullReciprocalSawtooth_of_dyadic` | 截断参数选择、所有对数与幂损失的吸收，从矩形 reciprocal 和到完整 sawtooth 界。 |
| 圆问题和除数问题 | [ReductionMain](CircleDivisor/EnergyV3/ReductionMain.lean)：`character_sawtooth_bound`、`main_of_reciprocal_rectangles`；[ArithmeticMain](CircleDivisor/EnergyV3/ArithmeticMain.lean)：`main_of_firstSpacing` | 复用已证明的双曲线分解与模四特征运算，最后结论涉及实际 `circleError` 和 `divisorError`；不再把最终误差项归约作为未证明的内部接口。 |
| 完整主定理 | [Main](CircleDivisor/EnergyV3/Main.lean)：`main_of_external_inputs`、`circle_and_divisor_error` | 由已证明的第一间距定理闭合上述链条，目标就是两个实际误差函数的统一幂界。 |

## 明确保留的外部输入

这些是命题参数，不是项目中新建的 Lean `axiom`。内部证明的完成意味着从这些准确陈述的外部定理推出目标；不意味着在 mathlib 中重新证明这些外部定理。

| 输入 | 文件与范围 |
| --- | --- |
| `CircleDivisor.GuthMaldague.GuthMaldagueInput` | [GuthMaldagueInput.lean](CircleDivisor/GuthMaldagueInput.lean)：实际 Schwartz 函数、闭 Fourier 支撑、规范角帽、活跃帽数阈值、具体包络权重和非负可数和。来源和固定归一化见 [GUTH_MALDAGUE_INPUT_NOTES.md](GUTH_MALDAGUE_INPUT_NOTES.md)。该旧说明中的“尚需连接”事项须以上文新增实际证明为准。 |
| `EnergyV3.LiYangInput` | [ExternalArithmetic.lean](CircleDivisor/EnergyV3/ExternalArithmetic.lean)：固定 `q` 的 Li–Yang v2 Lemma 4.4 接口，常数先于相位、BV 权重与尺度量化，六项 standing conditions 显式暴露。来源核对与 V 尺度层级见 [EXTERNAL_ARITHMETIC_V3_AUDIT.md](EXTERNAL_ARITHMETIC_V3_AUDIT.md)。 |
| `ClassicalInputs.DivisorBound` / `SpacingCount.NaturalDivisorEstimate` | 经典除数函数次幂界；两尺度内部计数只使用它，不假设所需四元组能量。 |
| `ElementaryReciprocal.GrahamKolesnikInput` | 对特定 reciprocal 相位的单变量经典 exponent-pair / 二阶导数估计；频率求和及二维统一范围在内部完成。 |
| `ClassicalInputs.TwoSquaresIdentity`、`BetaAtOne`、`HarmonicExpansion`、`VaalerApproximation` | 经典平方和公式、模四 beta 值、调和数展开和有限 Fourier 近似。它们与实际误差项之间的计算连接已经证明。 |

## 公理审计和复现

[verification/EnergyV3Axioms.lean](verification/EnergyV3Axioms.lean) 导入全部新版模块，
检查各分支主要声明及四个最终结论；输出保存在 [verification/EnergyV3Axioms.log](verification/EnergyV3Axioms.log)。
本轮成功输出仅包含 Lean/mathlib 通常使用的 `propext`、`Classical.choice`、`Quot.sound`，没有 `sorryAx` 或项目自定义公理。
`CircleDivisor/EnergyV3` 源码扫描没有 `sorry`、`admit` 或 `axiom` 声明。

审计包含 `FirstSpacingProof` 的统一与固定矩结论，以及 `Main` 的完整主定理和实际误差函数版本。
公理检查不消除定理的显式参数，也不能独自保证外部接口与文献完全等价；应同时核对上述外部输入列表及量词。

在项目目录运行匹配 `lean-toolchain` 的 Lake：

```text
lake env lean verification/EnergyV3Axioms.lean
```

本表的“完成”指内部论证的 Lean 证明已经闭合；外部定理仍按用户要求作为明确陈述的输入。


