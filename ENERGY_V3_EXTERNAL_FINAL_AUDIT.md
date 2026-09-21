# 新版外部接口最终数学核对

核对日期：2026-09-20。对象是 `manuscript/Gauss_circle_divisor_energy.tex` 的 9 月 8 日版本，以及当前 `CircleDivisor/EnergyV3`。本文件核对源定理与 Lean 外部命题的数学对应关系；编译和内核依赖检查另有构建／审计记录。外部定理作为明确假设保留，本文件不代替它们的 Lean 证明。

本轮没有发现所核对接口把本稿的新四项第一间距估计、密度界、一次质量或同射线／交叉能量界冒充外部定理。稿件第一间距定理的 **全 q 一致常数** 已由 `uniformFirstSpacing_of_external_inputs` 补足；常数与阈值均在 q 之前选择，详见第 5 节。

## 1. Guth–Maldague：对象匹配

采用 [arXiv:2206.01093v2，Theorem 2、§5、(13)、(29)](https://arxiv.org/html/2206.01093v2)。对应代码是 `GuthMaldagueInput.lean`，不是一个未解释的抽象 Fourier 分解输入。

| 核对项 | 代码及判断 |
|---|---|
| 截断锥面 | `cone` 为正片，竖坐标在 `[1/2,2]`。原文 §5 确实使用上端点 2；不能只看引言的上端点 1 就认定不匹配。限制到正片是此处所需特例。 |
| 离散尺度 | `radius n=4^n`，`scale j=2^(-j)`，`CapIndex j=Fin(2^j)`。所以细尺度为 `R^(-1/2)`，角宽为 `2π 2^(-j)`。 |
| 真实投影 | `capFunction` 是集合 `cap` 上的 sharp Fourier restriction；`fineChildren` 要求整个细帽包含在粗帽中。后续实际原子分配确实给出整个 Fourier 支撑位于一个细帽的结论。 |
| 物理包络 | `envelopeCoordinates` 的分母分别是 `2Rs²,2Rs,2R`；盒子条件为每个坐标绝对值不超过 `1/2`。展开后恰为指定框架中的三个包络不等式。 |
| 平移集合 | `Lattice=(Fin 3→ℤ)` 配合逆坐标映射给出全空间平移覆盖。闭盒共享边界不影响 Lebesgue 积分。 |
| 权重 | `baseWeight=∏(1+u_i²)^(-100)`。源 (13) 同时写乘积公式和 L¹ 归一化；代码以正的积分显式归一，补足该固定因子。这里的坐标将 `2U` 映到 `[-1,1]^3`，没有多取或少取一个随尺度变化的倍数。 |
| 活动数量 | `activeCount j f` 数的是该尺度全部非零粗投影，不是一个粗帽里的细帽数。`activeCount_le` 给 `≤2^j`，`contributing_mass_threshold` 内部推出 `α²s²≤CR^ε M_U`。 |
| 尾部分布与能量 | 左边使用 `α⁴` 和实际超水平集体积；右边使用 `|U|M_U²`，其中 `M_U=|U|⁻¹∫(Σ|f_θ|²)W_U`。`ℝ≥0∞` 的非负 `tsum` 保留无限包络和的真实含义。 |
| 端点 | `j∈Ioo 0 n` 对应源定理显示的严格范围 `R^(-1/2)<s<1`。命题仅要求充分大的 n；有限尺度由内部有界参数处理。 |

两个容易误读但并非新增假设的地方：

- 源 §5 的锥面用绝对值同时书写两个片，而随后帽为单块薄片的几何描述按单片理解。当前命题只用正片；对 Fourier 支撑位于正片附近的函数，另一片不贡献投影。此处没有要求一个包络同时控制两个相反生成方向。
- 一个固定权重归一因子会同时改变质量阈值及平方能量；在两处一并增大外部常数即可吸收。代码使用同一 `C`，并已内部证明增大 `C` 时贡献集合及右边单调。

`GuthMaldagueInput` 不包含任何依赖 K、L 的新能量或密度结论。它的常数在 `n,f,α` 之前，且没有后续矩参数 q，符合振幅积分所需的量词。

## 2. Li–Yang：引用层级与量词

采用 [arXiv:2308.14859v2，Lemma 4.4](https://arxiv.org/html/2308.14859v2#S4.SS2)，连同 (3.1)–(3.3)、(4.1)–(4.5)、(4.8)、(4.12)–(4.14) 和 Remark 4.5。引用的是完成第二间距优化后的界；没有重新假设该文的第一间距 Proposition 3.1。

当前最终调用对象是 **`EnergyV3.LiYangInput`**（`ExternalArithmetic.lean`），而非旧版 `ExternalInterfaces.LiYangInput`。它列出六项尺度条件：

`D≤R`，`DR≤H`，`64CH≤N`，`DN≤M`，`2C√H+1≤R`，`HN²≤MR²`，且 `D≥10`。

这是保守的调用范围；`HardReciprocal.hard_reciprocal_fixed_moment` 由实际 N、R 的可比关系和正幂裕量构造 `StandingConditions`，并非把“条件成立”作为最终用户前提。这里只要求源构造存在一个实际自然数 N 和正实数 R；没有声称任取可比 N、R 都能运行源的构造。

其余逐项核对：

- q 固定在所有构造常数之前，范围 `4<q≤9/2`。`HardReciprocal.hard_reciprocal_uniform` 分别调用四个 q 后取有限最大值，没有交换 `∀q∃C` 与 `∃C∀q`。
- `PhaseControl` 使用 `[1,2]` 上 C³、前三阶导数的上下界以及 `|F'F'''−3(F'')²|` 的下界。F 的加法常数不受限。BV 幅度的范数与变差都有固定界；复数幅度可分解成实、虚部处理。
- `caseA` 在整个所用 M 区间均加上 `H≥M^(-9)T⁴(log T)^(171/140)`，比源条件更严格。源 HTML (4.4) 的第一分支阈值含负的 `7/16`，与附近使用存在排印疑义；当前无条件加强的下界使本证明不依赖该符号判断。源的 `M>T^(9/16)` 分支在 `M≤√T` 下不会出现。
- Case B 的两个上界、两个候选长度的最小值及所有对数幂按稿件定义保留。额外的 Case B 到 Case A 比较是内部算术证明。
- `denominatorAdmissible` 同时保留 `R≤Q≤3H` 和 `Q≤D Q₂`。`spacingMajorized` 对所有允许的实际整数 K、L、η 和有界系数给上界，是对源最大值的安全上界。把 `L<K` 放宽到 `L≤K` 只扩大需要控制的集合。
- `etaSourceMoment` 是真实完整周期盒子的归一化积分；系数数组没有隐藏正性要求。与本稿周期盒子的等式和 η 区间覆盖在 `ExternalPeriodBridge`、`SpacingTransfer` 内证明。
- 源的 (4.6) 属于其第一间距代入步骤，不是代入之前 Lemma 4.4 的独立前提。V、V₀、V₁、V₂ 的优化属于外部引理的证明层级。若以后改引更上游的第二间距中间估计，就必须重新暴露这些构造条件，不能沿用本接口的解释。

稿件以已撤回的 BW17 版本定位部分构造条件；这项文献事实保留在稿件中。当前数值结论所依赖的外部断言明确归于 Li–Yang v2 Lemma 4.4；本审计不重新验证它的整个第二间距证明，也不把撤回版本的第一间距结论当作已验证输入。更详细的构造层级说明见 `EXTERNAL_ARITHMETIC_V3_AUDIT.md`。

## 3. Graham–Kolesnik 与互补区间

`ElementaryReciprocal.GrahamKolesnikInput` 只给实际单频率 m 和的两个经典上界。书目与章节见 [Graham–Kolesnik，Van der Corput's Method of Exponential Sums](https://www.cambridge.org/core/books/abs/van-der-corputs-method-of-exponential-sums/contents/6C1076907067B1EBB7636A4BADBCCDF9)。二阶导数估计的确切版本也可核对 [Vaughan 的原始论文 Lemma 2.1](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/59B09B47FEA0B1A68EC0D997B4E3D5D6/S0017089520000142a.pdf)，该处明确指向 GK Theorem 2.2。

相位为

`φ(m)=a yT/(m+σM)+b yT/M`，其中 `a∈[1/4,1]`、`σ∈[0,1]`、`m∈[M,2M)`。

因此全部必要阶导数与 `yT M^(-r-1)` 一致可比；b 只改变模长为 1 的公共因子。以下是本审计的直接代数核对：

- 指数对依次 `(0,1) →B (1/2,1/2) →A (1/6,2/3) →A (1/14,11/14) →B (2/7,4/7)`；主项 `(yT/M²)^(2/7) M^(4/7)=(yT)^(2/7)`。通常的低频余项 `M²/(yT)` 在本输入范围至多 1。
- `|φ''|` 与 `yT/M³` 可比，故二阶估计是 `O((yT/M)^(1/2)+M^(3/2)/(yT)^(1/2))`。由 `M≤√T,y≥1`，第二项至多 `T^(1/4)`，与输入完全吻合。
- BV 加权与半开／截断区间只改变统一常数。对 h 的求和、hard range 的补集选择、有限 T 区间、最终 `H T^(θ+ε)` 都位于内部证明；没有被藏入这个单频率外部命题。

本轮在线访问没有取得 GK 全书正文，故没有宣称逐页核验其指数对证明；上面的 A/B 有理数运算及特定相位尺度是独立核对，二阶导数定理正文已取得。

## 4. 经典输入的端点和规格

`ClassicalInputs.lean` 的五项命题均是具体公式，不能把定义它们等同于证明它们。

| 输入 | 规格核对 |
|---|---|
| `TwoSquaresIdentity` | 只要求 n≥1，计数包含顺序、正负号和零。与 [NIST DLMF 27.13.5–27.13.6](https://dlmf.nist.gov/27.13#E6) 的 Jacobi 系数公式一致；原点 n=0 由内部计数另行处理。 |
| `BetaAtOne` | 使用按正整数顺序的有限和极限，不错误宣称绝对可和。由 [反正切级数在 1 处的值](https://dlmf.nist.gov/4.24#E3)得到所需 π/4。 |
| `HarmonicExpansion` | 保留 `+1/(2n)` 及 `O(n^(-2))`。可以与 [DLMF 5.4.14](https://dlmf.nist.gov/5.4#E14)、[5.11.2 及余项](https://dlmf.nist.gov/5.11#E2)交叉核对；这足够支撑内部 O(1) 抵消。 |
| `DivisorBound` | `∀ε>0∃C>0∀n≥1,d(n)≤Cn^ε`，没有声称 C 对 ε 一致。它是经典约数界，供内部整数配对计数使用。 |
| `VaalerApproximation` | 给确切正弦多项式及 Fejér 余项。采用 `ψ(n)=−1/2`；在整数处正弦和为 0，余项恰为 1/2，所以该端点约定仍成立。 |

Vaaler 原文为 [Some extremal functions in Fourier analysis，1985](https://doi.org/10.1090/S0273-0979-1985-15349-2)。本轮 AMS PDF 返回访问错误，不能声称已在本轮逐页复核其全部系数。可访问的 [Carneiro 原始论文 §1、Theorem 1、§2](https://arxiv.org/html/0809.4049v2)明确区分对称锯齿值与 Bernoulli 周期函数端点，并给出相应极值三角多项式框架。这里的整数端点适配是上述直接计算，不是额外分析猜想。系数的正性、单调性和离散分部求和是在 `EnergyV3/ReductionWeight.lean` 等内部模块中处理的。

## 5. 新四项、指数与全 q 一致定量声明

当前 `EnergyV3.Arithmetic.fourTerm` 为

`(KL)^(q/2) + K L^(2q−5) + K^(q−2)L^(q−3) + K^(3q/4−2)L^(5q/4−2)`。

第三项已是新版配对细帽计数的 `K^(q−2)L^(q−3)`。平方根区间的两个幂条件、四个固定 q、三个分界点、最终端点等式都在 `Optimization.lean`／`Arithmetic.lean` 作为实数算术定理证明：

`q∈{201/50,17/4,22/5,9/2}`，分界 `−101/286,−251/736,−1/3`，

`θ=573/1828=0.3134573304157549…`，`E(−θ,9/2)=θ`。

这与旧版本 `0.3134615421015514…` 有区别，不能混用旧指数或旧第三项来描述本轮结果。

**定量声明已匹配：**`UniformFirstSpacingStatement` 明确采用稿件 Theorem 1 所需的 `∀ε>0 ∃Cε>0 ∀q∈(4,9/2]`，上界显式含 `q/(q−4)`。`FirstSpacingProof.lean` 中已编译的 `uniformFirstSpacing_of_external_inputs` 从 GM 与经典约数界证明该命题。

这不是从固定 q 版本交换量词所得：`AnalyticAssembly.uniform_class_moment_explicit_q` 在 q 之前取得统一的 GM、密度与能量常数及尺度阈值；`UniformFirstSpacingTransfer.uniformFirstSpacing_of_large_localized` 同样在 q 之前处理有限参数区间。最终构造先选 ε，再选常数与阈值，最后引入 q。`firstSpacing_of_external_inputs` 由统一版本推出旧的固定 q 命题。主指数的算术分支仍只取四个固定 q 的最大常数，因此也不要求 Li–Yang 的常数在连续 q 区间上一致。

## 6. 信任边界与检查范围

`Main.lean` 中 `EnergyV3.main_of_external_inputs` 将已证明的第一间距定理直接传入 `ArithmeticMain.main_of_firstSpacing`，得到 `MainTheoremStatement`；`circle_and_divisor_error` 显示实际圆误差、除数误差及指数 `573/1828+ε`。最终类型有四个参数：GM、新版 Li–Yang、GK、`ClassicalInputs.Inputs`；展开最后的结构后，共八项明确外部命题。第一间距、局部密度、能量和矩形倒数和均不再作为最终定理的前提。

本轮文本扫描的 `EnergyV3`、`GuthMaldagueInput.lean`、`ClassicalInputs.lean` 没有 `sorry`、`admit` 或自定义 `axiom` 声明。文本扫描不替代内核依赖检查，也不替代已陈述外部命题的真值证明。原稿中局部化、实际质量、真实权重积分、配对能量和误差项归约均应由具名内部定理承担；这些不能因写成一个 `Prop` 就变成允许的外部输入。
