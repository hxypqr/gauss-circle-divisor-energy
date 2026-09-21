# 新版最终验证记录

日期：2026-09-20。项目：`D:/lean4/CircleDivisor`。

## 结论

2026 年 9 月 8 日稿件的主定理内部证明链已经闭合。最终指数是 `573/1828`。主定理仅保留 GM、Li–Yang、GK 和五项经典输入；所有这些输入都是明确的命题参数。

已编译的最终声明：

- `CircleDivisor.EnergyV3.uniformFirstSpacing_of_external_inputs`：全 q 一致的四项第一间距界，常数先于 q，显式保留 `q/(q−4)`。
- `CircleDivisor.EnergyV3.firstSpacing_of_external_inputs`：固定 q 版本。
- `CircleDivisor.EnergyV3.main_of_external_inputs`：主定理。
- `CircleDivisor.EnergyV3.circle_and_divisor_error`：显示真实误差函数与有理指数的主定理。
- `CircleDivisor.EnergyV3.Corollaries.sqrt_moment_of_external_inputs`：统一平方根区间推论。
- `CircleDivisor.EnergyV3.Corollaries.nine_halves_moment_of_external_inputs`：q=9/2，新版范围 `L^(11/7)≤K≤L³`。

## 机器检查

| 检查 | 结果与记录 |
| --- | --- |
| 整体构建 `lake build` | 成功，8758 jobs；[日志](build_energy_v3.txt)。根模块导入所有新版模块。日志中有非致命的代码风格／弃用提示，无构建错误。 |
| 全命名空间公理检查 `lake env lean Audit.lean` | 成功，2133 个 `CircleDivisor` 导出 theorem 声明全部通过；[日志](axioms_energy_v3.txt)。 |
| 分支及最终定理 `#print axioms` | [检查文件](EnergyV3Axioms.lean)、[输出](EnergyV3Axioms.log)。 |
| 占位证明扫描 | `CircleDivisor` 源码中无 `sorry`、`admit`、自定义 `axiom` 或 `native_decide`。公理检查同时递归检查声明的真实依赖。 |

允许的公理只有 `propext`、`Classical.choice`、`Quot.sound`。特别地，两个最终主定理、统一第一间距结论和平方根推论的依赖均在此列表内。

这证明内部推导通过 Lean 内核检查，不证明外部参数本身。来源与规格的人工核对另见 [外部接口审计](../ENERGY_V3_EXTERNAL_FINAL_AUDIT.md)，包括文献访问限制及源文排印疑义。逐节对应见 [证明地图](../ENERGY_V3_PROOF_MAP.md)。

## 工具链与原稿校验

- Lean：`leanprover/lean4:v4.32.1`。
- mathlib：`520045ab14e26149ee970e2e617ca04b09bde5d6`，由 `lake-manifest.json` 固定。
- 原稿 TeX SHA256：`A07DDF75DB987C12228D9FD8CBAEA79BAFCE09C254D9E6DB1715967099F97360`。
- 原稿 PDF SHA256：`97BD8220CF1C0E180C68C2DA9E0009C5E5B9E4D4717BF37EA4728A2EB84EC03F`。

项目内的两份新版原稿与用户指定文件哈希完全一致。没有改写原稿来迁就形式化。

复现命令：

```text
lake build
lake env lean Audit.lean
lake env lean verification/EnergyV3Axioms.lean
```

早期的 `STATUS.md`、`build_round2.txt`、`axioms_round2.txt` 和旧 README 属于旧稿或中途状态。本记录及上述新版日志为本轮最终状态。
