# 外部依赖与内部证明边界

本文件记录文献核对与形式化现状。文献中的定理正确，并不表示当前工程已经正确构造其 Lean 实例；两者分开记录。

## 两项主要文献输入

1. Guth–Maldague, *Amplitude dependent wave envelope estimates for the cone in R³*, arXiv:2206.01093v2, Theorem 2 及 §5 的约定。
   - 原文：https://arxiv.org/html/2206.01093v2
   - 已核对：阈值中的 `#τ` 是该尺度活跃的粗帽总数；fine projections 是 sharp restrictions；实际加权 envelope 积分不能先替换成周期平均。
   - 已在 `GuthMaldagueInput.lean` 写成具体的正锥面特例输入：实际角帽、锐投影、frame、整数平移格、归一化权重、活跃帽、真实质量与非负可数和；采用 `tsupport` 保留边界闭包要求。外部定理没有在 Lean 内重证，也未声明全局 `axiom`。
   - **仍待内部应用连接**：本文 χF₀ 经线性变换／两网格分配满足输入的精确假设，包络 Jacobian、权重重叠、核衰减、局部密度与能量总和。详见 `GUTH_MALDAGUE_INPUT_NOTES.md`。
2. Li–Yang, *An improvement on Gauss's circle problem and Dirichlet's divisor problem*, arXiv:2308.14859v2, Lemma 4.4、(4.8)、(4.12)。
   - 原文：https://arxiv.org/html/2308.14859v2
   - 已核对：稿件 §5 引用的两个 block 长度、参数关系与 large-sieve 表达式相符；原文条件 (4.6) 是插入其特定 first-spacing bound 时使用的条件，不能随意附加到通用接口或从其他必要条件中删除。
   - 已在 `ExternalInterfaces.LiYangInput` 写出带真实和、C³ 非退化、BV 控制、量词常数及全部参数范围的输入命题。`ExternalPeriodBridge.lean` 已证明原文与本文周期盒的真实归一化积分相等，并将 η moment 接到 `coneMoment`。
   - **适用范围修正**：Case A/B 本身并不推出 R≤H；`LiYangInput` 显式保留 `BlockSeparation`。稿件 §6.3 的 hard-range 分离是必须证明的内部步骤。`BlockSeparation.lean` 本轮已给统一指数裕量 1/1000、统一幂阈值及实际比较因子吸收，仍须与外部实际选择的 block 和全文渐近流程接合。反例参数及原文 Remark 4.5 见 `EXTERNAL_INTERFACE_AUDIT_ROUND2.md`。

本文未采用已撤回的 Bourgain–Watt 稿中的 first-spacing 数值结论作为输入。

## 已有正式假设语句的经典输入

`ClassicalInputs.lean` 中使用 `Prop` 和结构字段，不引入全局 `axiom`：

- `DivisorBound`：∀ε>0，∃C>0，∀n≥1，τ(n)≤C n^ε。`SpacingCount` 已在此唯一输入下完成 Lemma 3.2 的内部计数，包括实数参数取整。
- `TwoSquaresIdentity`：仅对 n≥1，r₂(n)=4∑_{d|n}χ₄(d)，左边是实际整数解集合的有限基数。
- `BetaAtOne`：∑_{1≤d≤N}χ₄(d)/d → π/4。这里使用顺序部分和的极限；没有将条件收敛级数误写成无条件 `HasSum`。
- `HarmonicExpansion`：H_n=log n+γ+1/(2n)+O(n^-2)，量化为统一 C/n² 的绝对误差界。
- `VaalerApproximation`：用真实三角函数给出有限近似和 Fejér 余项；采用 ψ(n)=-1/2 的整点约定。

这些输入的投影引理仅展示如何使用假设，不能当成这些经典定理的无条件新证明。

## 尚需精确形式化的其他标准输入

- Graham–Kolesnik 中 reciprocal phases 的 exponent pair (2/7,4/7) 区间和估计、second-derivative estimate，包含参数的一致性。随后 h 求和及 BV 分部求和属于内部步骤。
- 若不从 mathlib 推导，Vaaler 系数函数的端点光滑性／统一 BV 界须单独给准确的标准输入。有限近似不等式本身不自动给此范数界。

## 一致性提醒

稿件使用 q=q(x)，不能直接交换 `∀q∃C` 与 `∃C∀q`。本轮 `UniformMoment.lean` 已针对真实指数和证明有限 q 网格归约：利用 `|F|≤4KL`、各单项随 q 单调和任意小的幂损失，严格得到 `FirstSpacingStatement ↔ FirstSpacingUniformStatement`。**第一间距的 q 一致性不再是一项额外输入或未解决的逻辑问题**；但这两个命题本身都还未证明。

Li–Yang 的输入仍忠实保留固定 q 量词。实际优化应用中取有限 q 网格并吸收指数误差的连接，还须在内部完成。

`ReciprocalPhase.lean` 已实际证明 a/(u+s)+b 的导数、非退化和统一 PhaseControl，覆盖除数与圆问题所需倒数相位。这不再是尚待输入的相位公式。

`FinalAssembly.SawtoothBounds` 是明确标注的、尚未证明的**内部目标**。`main_of_sawtooth_bounds` 只证明：如果这些真实锯齿和已获得指数界，那么已有经典输入和本轮算术归约足以推出主定理。它没有把锯齿和界提升为可信外部输入。

内部未完成步骤均列于 README；没有将其包装为文献的“正确外部输入”。
