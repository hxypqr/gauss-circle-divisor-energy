# 新版算术接口核对（2026-09-20）

实际引用的是 Li–Yang v2 的 **Lemma 4.4**，不是只含某个 minor-arc 主项的中间不等式：
[原文 §4.2](https://arxiv.org/html/2308.14859v2#S4.SS2)。
其参数定义为 (4.1)、(4.8)、(4.12)，源的 (4.13)–(4.14) 与 Remark 4.5 另要求核实尺度。
本稿所需的 BV 权重已在源 (4.1) 中，初始矩形见源 §4.2 的展示式。

`EnergyV3.LiYangInput` 保留固定 q 在常数之前的量词；常数在 F、g、G、H、M、T 之前。
它使用实际 `etaSourceMoment`、实际 `reciprocalSum` 和实际有限参数 majorant。
`StandingConditions` 显式要求：R 足够大、R≤H、64CH≤N、N≤M/10、
2C√H+1≤R、HN²≤MR²。D≥10 保证 N≤M/10。前四项保留更强的固定分离因子 D。
六项均在 `HardReciprocal` 中由内部实数不等式提供；不是待证明输入。

V、V₀、V₁、V₂ 的层级必须区分：源在 Lemma 4.4 之前使用 VB(A,Q;V)，并说明第二间距优化已经完成；
Lemma 4.4 本身不把 V₀、V₁、V₂ 作为独立调用假设。它们属于该外部定理的证明构造。
因此这里不重新把源证明的 V 条件放入外部定理的调用接口。
新版稿件附录的 V 精确恒等式、缩短 N 的 60/17 幂变化、Case A/B 的幂裕量仍已独立形式化于
`EnergyV3.Construction`。仅凭 N 与名义值可比不能推导 Case A 零幂裕量处的任意固定常数分离；
如改为直接引用更上游的第二间距中间估计，就必须再记录其确切小长度因子。这并非当前引用层级。

源 (4.6) 是其特定 first-spacing 代入后的额外要求：原文 (4.15)、(4.20) 说明此事。
新版接口在代入前引用 Lemma 4.4，故没有偷加或偷用源的 first-spacing 估计。

`ElementaryReciprocal.GrahamKolesnikInput` 是另一个明确外部输入：GK Chapters 2–3 的
(2/7,4/7) exponent pair 与 Theorem 2.2 二阶导数估计，专用于 a/(t+σ)+b，
a∈[1/4,1]、σ∈[0,1]、b 任意、BV 幅度有统一界。该命题只断言单个实频率的 m 和；
频率求和、所有参数区间、有限 T 区间、四矩常数合并均已内部证明。
这是一维经典估计的接口，并没有把稿件的二维目标界当成外部定理。

`ArithmeticMain.main_of_firstSpacing` 的内部未决前提仅为 `EnergyV3.FirstSpacingStatement`。
其他前提分别是上述 Li–Yang/GK 输入及 two-squares、beta(1)、harmonic、Vaaler 四个经典输入。
该定理不能被报告成已无条件证明主定理；仍须由解析分支提供第一间距定理。
