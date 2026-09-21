# 第二轮：第 7 节误差项归约

本轮在 `CircleDivisor/DiscrepancyReduction.lean` 完成了**实际圆点计数、实际除数求和函数到锯齿和的归约**。这不是用同名抽象序列替代算术对象，也没有把稿件的内部归约作为外部假设。

## 已证明

- `divisorSummatory_hyperbola`：实际 `divisorSummatory X` 的精确双曲线恒等式，右侧为 `2 Σ_{1≤m≤U} floor(X/m) − U²`。
- `divisorError_sawtooth`：仅输入 `ClassicalInputs.HarmonicExpansion`，证明所有实数 `X ≥ 1` 上的 (7.4)。若谐和展开常数为 `C`，则 `|Δ(X)+2 Σ_{m≤floor(sqrt X)} ψ(X/m)| ≤ 12+8C`。
- `circleCount_eq_sum_twoSquares`：将实际 `circleCount` 的有限整数点集按整数平方半径分纤维；单独处理原点。
- `circleCount_character_divisors`、`circleCount_hyperbola`：仅输入 `TwoSquaresIdentity`，从系数公式严格推出 (7.5)、(7.6)，包括原点的 `+1`。
- `partialSum_floor_eq_floorDifference`：把实际字符部分和连接到 (7.7) 的两项取整差，适用于每个非负实数，包括跳跃端点。
- `beta_tail_bound`：仅输入有序极限 `BetaAtOne`，内部证明 (7.8) 的显式版本：`|π/4−Σ_{d≤U} χ₄(d)/d−(1/2−A(U))/U| ≤ 1/U²`，对全部整数 `U ≥ 1` 一致成立。
- `circleError_sawtooth`：仅输入 `TwoSquaresIdentity` 和 `BetaAtOne`，证明所有 `X ≥ 1` 上的 (7.9)，其三项锯齿和定义为 `circleSawtooth`，且 `|R(X)−circleSawtooth X (floor(sqrt X))| ≤ 23`。
- `vaaler_sum_error`、`vaaler_sum_eq`、`sawtooth_sum_le_fourier`：从准确的有限 Vaaler 输入推得第 7.1 节使用的有限 Fourier 总和与误差不等式。正弦主和保留整个 `h` 和的绝对值；余弦误差和保留符号，没有不合法地逐项取绝对值。

β 尾项的形式证明使用二阶离散部分求和：`χ₄(n+1)−χ₄(n)=1−2A(n)` 给出第二个有界离散原函数。对修正后的部分和建立单调上下界，再取 `BetaAtOne` 的有序极限。这是对稿件积分分部求和论证的等价替代证明，没有新增外部输入。

## 尚未完成

第 7.1 节从 Proposition 6.3 的矩形指数和估计推到 Lemma 7.1 的完整链仍未完成：

1. 具体权重 `W(h/(Y+1))/h` 在二进区间上的一致离散变差界，以及相应有限部分求和接口。
2. Fejér 权重的区间变差界和二进频率区间的求和组织。
3. `Y=floor(M T^{-θ})` 的参数范围、常数以及对数损失的 ε 吸收，和实际指数和定义之间的连接。
4. Lemma 7.1 对 `m≤floor(sqrt X)` 的二进分解；字符项按 `d=4j+1,4j+3` 的集合重排及两个 `j=0` 边界项。既有 `Sawtooth` 文件的移位相位代数恒等式仍需要接到这些有限集合求和。

因此，本文件已经完整证明 (7.4) 与 (7.9) 的算术归约，但**不声称已经证明 Theorem 1.1 的指数界**。

## 疑点与检查结果

本轮没有发现第 7.2、7.3 节归约中的数学 gap。尤其 `O(1)` 消去、字符尾项的 `U^{-2}` 阶、非整数 `X`、锯齿函数跳点、原点以及 `1/4,3/4` 移位均已由 Lean 验证。第 7.1 节以上尚未完成内容属于未验证的形式化工作；本轮没有据此判定其结论错误。

验证入口：`lake build CircleDivisor.DiscrepancyReduction`。
公理审计入口：`lake env lean verification/discrepancy_round2_audit.lean`。
本文件没有 `sorry`、`axiom` 或 `native_decide`；外部数学输入通过显式命题参数传入。
