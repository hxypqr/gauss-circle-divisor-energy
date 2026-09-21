# 第二轮：外部输入核验和实际积分连接

核验日期：2026-09-07。对应代码：`CircleDivisor/ExternalInterfaces.lean`
和 `CircleDivisor/ExternalPeriodBridge.lean`。
此文件中的 `LiYangInput` 是带明确量词的外部输入命题，不是已经证明的 Lean 定理，
也没有声明 `axiom`。`liYang_fixed_q` 只是从这个输入取出固定 q 的结论。
本轮没有把稿件 Theorem 1.2、Proposition 6.3 或 MainTheoremStatement 当成外部输入。

## 一手来源

- [Li–Yang arXiv:2308.14859v2](https://arxiv.org/html/2308.14859v2)：
  §3.1 式 (3.1)–(3.3)，§4.1 式 (4.1)–(4.5)、(4.8)，
  §4.2 式 (4.12)–(4.14)、Lemma 4.4，以及 **Remark 4.5**。
- [Guth–Maldague arXiv:2206.01093v2](https://arxiv.org/html/2206.01093v2)：
  Theorem 2、§2 式 (13)、§5 式 (29)–(30) 和其前后的定义。

## 新完成的实际对象与内部证明

代码使用原工程的 `coneSum`、`coneMoment` 和 `reciprocalSum`。
没有用任意函数替代这些振荡和。

1. `BVControl` 直接使用 mathlib 的 `eVariationOn`，并控制 [1,2] 上的 supremum。
   `BVControl.boundedVariation` 已证明这些条件确实给出 bounded variation。
2. `PhaseControl` 明确要求 `ContDiffOn ℝ 3`，前三阶导数的上下界，以及
   `|F' F''' - 3(F'')²|` 的正下界。闭区间端点使用 `iteratedDerivWithin`，
   不要求相位在区间以外的无关取值具有光滑性。
3. `etaMoment` 定义真实的 η 小盒积分及其体积归一化。
   `etaSourceMoment` 单独保留 Li–Yang 原文在前两个坐标使用 [-1,1] 的版本，
   没有把它与原工程 [0,1] 版本直接定义成相同对象。
4. `coneSum_continuous` 和 `coneMoment_integrableOn` 已证明实际和的连续性和
   q≥0 时的盒上可积性。
5. `etaMoment_le` 已证明真正的积分不等式
   `etaMoment K L η q a ≤ (η*K*L) * coneMoment K L q a`
   （K,L,η>0，q≥0，ηKL≥1）。这是稿件 (5.10) 的有序盒核心，
   不是把归一化 Lq 范数误当作对积分域单调。
6. `translatedCoefficients_norm` 和 `coneSum_translate_third` 证明平移第三坐标
   确实只给每个系数乘单位模复数。
   `coneSum_integer_periods` 证明前两个坐标的真实整数周期性。
7. `SpacingParameters` 保留整数 K,L、η>0、1≤L≤K≤η⁻¹≤KL，以及
   K,L,η,ηKL 与 N,H,R,Q 的固定因子比较。
   `etaMoment_le_of_spacingParameters` 已把参数约束接到上述积分比较。
8. `ExternalPeriodBridge.etaSourceMoment_eq_etaMoment` 已通过一般 n 维产品积分的
   Fubini 公式、紧盒可积性和一维周期积分，**完整证明源文 [-1,1]² 与稿件 [0,1]²
   的实际归一化矩相等**。`etaSourceMoment_le_of_spacingParameters` 将这个
   等式及实际盒比较组合起来，直接连接源文的矩和原工程 `coneMoment`。

## 发现并纠正的外部接口过强表述

稿件 §5.1 把 Case A/B 和 M≤sqrt T 描述为充分条件，随后声称所构造参数有
R≲H≪N。**若按该段的全称量词直接理解，这个范围表述不充分。**

具体地，取 H=1，M=T^(1/2)。T 足够大时满足 Case B 的两条上界，但

```
NB = T^(23/80) (log T)^(969/5600)    （最终取第一支）
R  ≍ T^(17/160) (log T)^(-969/11200)
```

所以 R/H→∞，没有非空的 R≤Q≤3H 范围。此现象不是形式化工具的限制。
**Li–Yang Remark 4.5 本身明确提醒 R≤H 不总成立；失败的部分用初等估计处理。**
因此不能把“所有 Case B 参数均存在满足 R≤H 的 block 且裸 Lemma 4.4 可用”
写成可信外部输入。

本轮 `LiYangInput` 采取保守且可检查的接口：外部提供与指定长度可比的 N,R；
large-sieve 部分明确以 `BlockSeparation` 为前提，要求

```
D ≤ R,    D*R ≤ H,    64*C*H ≤ N,    D*N ≤ M.
```

这些是具体数值前提，不是任意未解释的 `Prop`。最终使用者必须在内部证明它们。
稿件 §6.3 已给出 hard range 中 R≫1、R≪H≪N≪M 的正幂余量论证，
也说明 Case B 的 NB≥常数*NA 如何保持分离。因此这个发现首先要求修正
§5.1 的适用范围表述及形式接口；**没有由此得到主定理的反例**。

原工程已有 `Arithmetic.actual_caseB_separations`，在 exponent-level 的
`blockA≤n≤blockB₂` 前提下证明 `h<n`、`0<lExponent`、`n<m`、
`0<radiusExponent`；其中 `lExponent=h-radiusExponent`。
`Arithmetic.hard_spacing_separations_with_logs` 覆盖含对数的 Case A。
本轮后续 `BlockSeparation.lean` 已把这些严格指数不等式提升为统一的 1/1000 margin，
并证明统一充分大 T 阈值、固定比较因子及 R² 平方根比较的吸收。
`LogScale.lean` 也已证明实际 block 长度与幂模型相等、loglogT/logT 最终足够小。
尚须处理外部实际选择的 N,R、整数舍入和全部前提的装配，不能把已证组成引理当作
完整 source 调用已经发生。

源文还保留 Q≤3H≤3N/(64*C₂)。新接口的 `denominatorAdmissible`
明确包含 Q≤3H，而不仅是 Q≲Q₂。q 常数、比较常数、phase bounds 和 sufficiently
large M,T 的顺序都写进了量词。

## 哪些额外条件确实不应该加入

Li–Yang 的 (4.6) 是将其特殊 first-spacing bound 插入 Lemma 4.4 后，在 §4.3
得到的条件。它不属于裸 large-sieve 输入。本轮接口没有加入 (4.6)，与稿件的区分一致。
原文使用的 phase 条件只涉及导数，所以新接口没有限制 F 的任意加性常数。

`spacingMajorized` 用“每个 admissible Q,K,L,η 及每个 bounded array 都被 B 控制”
表达一个有效的统一上界。这个要求允许扩大源文 maximum 的索引集，不依赖可能为空、
可能无界的实数集合的 `sSup`。

## Guth–Maldague 对照结果

本轮核验没有发现下列来源错配：

- §5 确实允许 1/2≤|ξ₃|≤2 的截锥，不能只读取 Introduction 的较窄截断。
- §5 的 angular caps 是圆柱角区间的 **sharp Fourier restriction**，不是必须
  平滑的分割。因此保留整个 Fourier atom 的两套网格方法与该定义相容。
- §5 使用真正的 `W_U` 加权平方函数；权重按 §2 式 (13) 的方式定义，
  与稿件固定倍数的三维 polynomial-tail product 一致。
- 第二网格的旋转依赖 P，但旋转是正交变换。定理对旋转后的函数可用；仍须在内部
  证明投影、积分、envelope 及 active-cap count 在这个变换下对应。
- Theorem 2 的 `#τ` 统计同一尺度所有活跃 coarse caps，不是某个 coarse cap
  中的 fine-cap 个数。稿件的 `n_s` 采用了正确的含义。

精确接口还须留意：Introduction 的阈值写在 mass 上，§5 (30) 写在 L²-average
norm 上；平方会同时改变常数及 R 的小指数。重新选辅助 ε 可以一致化，不能不加
说明地把相同 C、相同 ε 的两式视为字面等同。

本模块不重复定义 Guth–Maldague 输入。本轮另一模块 `GuthMaldagueInput.lean`
已给出具体的 R=4^n 层级角区间、截锥邻域、实际 sharp Fourier restriction、
三维 frame/envelope、整数平移索引、归一化 W_U、active-cap cardinality，
以及以 ENNReal 表达的所有平移 envelope 的非负无穷和。
独立源码复核确认 frame、权重坐标和 active-count 与以上来源相容。
这消除了此前的任意 Prop 外壳问题；仍须证明稿件的实际局部化函数与这些
具体投影、coarse/fine containment、平铺和旋转对象逐项对应，才能真正应用输入。
另已向该模块作者指出 `Function.support ⊆ open neighborhood` 与
`tsupport ⊆ open neighborhood` 的差别，建议采用后者避免无说明的边界闭包转换。

## q 一致性与其他尚未完成的连接

`LiYangInput` 保留固定 q 量词，不擅自交换 `∀q∃C` 与 `∃C∀q`。
这不是已发现的致命 gap：本轮 `UniformMoment.lean` 已完整证明真实
`|F_a|≤4KL`、moment 比较、四项 monomial 的 q 单调性和有限下取 q 网格，
并得到 `firstSpacing_uniform_of_pointwise` 及 `firstSpacing_uniform_iff_pointwise`。
因此 first-spacing 的 compact-uniform 性现已由逐 q 版本内部推出，不是额外外部输入。
Li–Yang 最终优化取有限 q 网格并以连续性吸收指数误差的连接仍待完成。

仍待连接的标准步骤包括：

- 在比较常数导致 η 盒略大时，完成有限平移覆盖及体积因子的证明；
- 源文闭端点/部分矩形与工程半开 dyadic sum 的 endpoint-indicator 归一化，
  及该归一化的 BV 常数控制；这属于 source-compatible specialization，
  本文件尚未单独提供这一标准转换的内部 Lean 证明；
- 真实 reciprocal phases 的统一 `PhaseControl` 本轮已在 `ReciprocalPhase.lean` 完成，
  包括实际三阶导数及曲率行列式；尚须将这些已证实例接入最终的 large-sieve 调用；
- 从 hard range 及指定 block 比较证明 `BlockSeparation`，再将四项 first-spacing
  bound、所有 Q 的估计和最终 exponent optimization 接到实际 `reciprocalSum`。

因此，本模块的编译成功表示上面的内部引理以及具体输入语句通过 Lean 检查，
不表示已经证明外部论文、first-spacing 主估计或最终圆/除数误差主定理。

验证：`lake build CircleDivisor.ExternalInterfaces` 及
`lake build CircleDivisor.ExternalPeriodBridge` 成功。
对实际 η 盒比较、整数周期、第三坐标平移、固定因子分离及输入提取运行
`#print axioms`；仅出现 Lean/mathlib 标准的 `propext`、`Classical.choice`、
`Quot.sound`，未出现 `sorryAx` 或新增数学公理。
新完成的 `etaSourceMoment_eq_etaMoment` 与
`etaSourceMoment_le_of_spacingParameters` 也通过同一公理审计。
