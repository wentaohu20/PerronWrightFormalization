# 概率主定理与相关定义索引

本页索引 Chapter 3 的实际 Aldous 阶乘密度与确定性、有限型/紧致型局部公式，以及实际 Brownian 窗口和全局点过程极限。链接均指向源码中的定义或定理开始行；这里只说明源码对象与定理语义，不替代运行验证，也不报告构建或审计状态。

## 1. 主定理入口

### 1.1 实际 Brownian 阶乘密度与确定性

| 完整 Lean 名称与位置 | 内容 |
| --- | --- |
| [PerronWright.BrownianActualFactorialDensity.actual_ordered_source_factorial_density](../PerronWright/Probability/BrownianActualFactorialDensity.lean#L64) | 任意阶、有序不同完整 excursion、各槽 surplus 与任意耦合非负 Borel 长度测试的实际密度公式。 |
| [PerronWright.BrownianActualFactorialDensity.actual_window_factorial_density](../PerronWright/Probability/BrownianActualFactorialDensity.lean#L136) | 正 size 闭窗口中的内在 factorial-measure 密度公式；允许不同槽窗口重叠。 |
| [PerronWright.BrownianActualArbitraryWindowDeterminacy.actual_cell_countLaw_eq_of_factorial_lintegrals](../PerronWright/Probability/BrownianActualArbitraryWindowDeterminacy.lean#L36) | 实际密度的 mixed factorial moments 确定不交 cells 的联合计数律。 |
| [PerronWright.BrownianActualArbitraryWindowDeterminacy.actual_windowLaw_eq_of_density_factorial_lintegrals](../PerronWright/Probability/BrownianActualArbitraryWindowDeterminacy.lean#L95) | 密度 moments 确定任意正 size 闭窗口的完整 weak-Borel 点过程律，包括单点窗口。 |

最后一个定理对比较律只要求不交、Lebesgue 边界零测 size cells 的密度 factorial 积分等式；比较律的可积性、矩确定所需级数与完整窗口律确定性由证明处理，并非额外输入前提。

### 1.2 有限型与紧致型局部公式

| 完整 Lean 名称与位置 | 内容 |
| --- | --- |
| [PerronWright.FiniteIrreducibleLocalMainTerminal.eventually_uniform_paper_floor_factorial_density](../PerronWright/Probability/FiniteIrreducibleLocalMainTerminal.lean#L34) | 固定 types、最终一致的有界整数 count 误差下，对窗口内所有 size、bounded surplus、所有实现这些 counts 的实际 assignments 一致成立的 raw-time/floor 公式。 |
| [PerronWright.CompactAnnealedFactorialUniform.factorial_uniform_bounded_surplus](../PerronWright/Probability/CompactAnnealedFactorialUniform.lean#L44) | `IsRegularCritical` 与 `QP` 下，实际 annealed 图律的 floor factorial expectation 对整个正 size 窗口与 bounded surplus tuples 一致收敛。 |

有限型定理直接展示论文时间 `1 + λ n^(−1/3)` 和字面 floor；紧致型定理使用对所有 n 有定义的非负时间约定，后者最终等于论文时间。

### 1.3 实际 Brownian 极限的十二个入口

这些定理均位于 [ModelActualBrownianLimits.lean](../PerronWright/Probability/ModelActualBrownianLimits.lean)。有限型要求 `M.IsCritical` 与最终一致的 `O(1)` fibre-count 误差，允许一般不可约核；紧致型要求 `M.IsRegularCritical` 与 `M.QP`。窗口结论要求 `0 < a ≤ b`、surplus 上界 `R`。定理陈述是完整序列的收敛，不仅是子列；其前提不额外假定 Brownian 密度或 Brownian-law identification。

| 完整 Lean 名称与位置 | 结论 |
| --- | --- |
| [PerronWright.ModelActualBrownianLimits.finite_windowLaw_tendsto_actual_Brownian](../PerronWright/Probability/ModelActualBrownianLimits.lean#L45) | 有限型未标记窗口律。 |
| [PerronWright.ModelActualBrownianLimits.finite_processLaw_tendsto_actual_Brownian](../PerronWright/Probability/ModelActualBrownianLimits.lean#L63) | 有限型未标记全局律。 |
| [PerronWright.ModelActualBrownianLimits.finite_markedWindowLaw_tendsto_actual_Brownian](../PerronWright/Probability/ModelActualBrownianLimits.lean#L80) | 有限型实际经验标记窗口律。 |
| [PerronWright.ModelActualBrownianLimits.finite_markedProcessLaw_tendsto_actual_Brownian](../PerronWright/Probability/ModelActualBrownianLimits.lean#L97) | 有限型实际经验标记全局律。 |
| [PerronWright.ModelActualBrownianLimits.finite_starredProcessLaw_tendsto_actual_Brownian](../PerronWright/Probability/ModelActualBrownianLimits.lean#L113) | 有限型星号未标记全局律。 |
| [PerronWright.ModelActualBrownianLimits.finite_starredMarkedProcessLaw_tendsto_actual_Brownian](../PerronWright/Probability/ModelActualBrownianLimits.lean#L128) | 有限型星号实际经验标记全局律。 |
| [PerronWright.ModelActualBrownianLimits.compact_windowLaw_tendsto_actual_Brownian](../PerronWright/Probability/ModelActualBrownianLimits.lean#L158) | 紧致型未标记窗口律。 |
| [PerronWright.ModelActualBrownianLimits.compact_processLaw_tendsto_actual_Brownian](../PerronWright/Probability/ModelActualBrownianLimits.lean#L173) | 紧致型未标记全局律。 |
| [PerronWright.ModelActualBrownianLimits.compact_markedWindowLaw_tendsto_actual_Brownian](../PerronWright/Probability/ModelActualBrownianLimits.lean#L187) | 紧致型实际经验标记窗口律。 |
| [PerronWright.ModelActualBrownianLimits.compact_markedProcessLaw_tendsto_actual_Brownian](../PerronWright/Probability/ModelActualBrownianLimits.lean#L201) | 紧致型实际经验标记全局律。 |
| [PerronWright.ModelActualBrownianLimits.compact_starredProcessLaw_tendsto_actual_Brownian](../PerronWright/Probability/ModelActualBrownianLimits.lean#L215) | 紧致型星号未标记全局律。 |
| [PerronWright.ModelActualBrownianLimits.compact_starredMarkedProcessLaw_tendsto_actual_Brownian](../PerronWright/Probability/ModelActualBrownianLimits.lean#L229) | 紧致型星号实际经验标记全局律。 |

## 2. 模型、临界假设与 Perron 参数

| 完整 Lean 名称与位置 | 语义 |
| --- | --- |
| [PerronWright.FiniteIrreducibleModel](../PerronWright/Model/FiniteIrreducibleModel.lean#L22) | 有限正 type weights、总和一、对称不可约核。非负性来自不可约核条件；不要求 strictly positive 或非周期。 |
| [PerronWright.FiniteIrreducibleModel.meanMatrix](../PerronWright/Model/FiniteIrreducibleModel.lean#L44) | 平均矩阵 `κ diag(μ)`。 |
| [PerronWright.FiniteIrreducibleModel.IsCritical](../PerronWright/Model/FiniteIrreducibleModel.lean#L51) | 实际平均矩阵的谱半径等于一。 |
| [PerronWright.FiniteIrreducibleModel.perronFunction](../PerronWright/Model/FiniteIrreduciblePerronQuantities.lean#L124) | 正固定函数，归一化为 `Σ μₐφₐ = 1`。 |
| [PerronWright.FiniteIrreducibleModel.alpha](../PerronWright/Model/FiniteIrreduciblePerronQuantities.lean#L139) | `Σ μₐφₐ²`。 |
| [PerronWright.FiniteIrreducibleModel.beta](../PerronWright/Model/FiniteIrreduciblePerronQuantities.lean#L142) | `Σ μₐφₐ³`。 |
| [PerronWright.CompactBJRModel](../PerronWright/Model/CompactBJR.lean#L29) | 紧致度量 type 空间、full-support 概率测度与连续对称非负核。 |
| [PerronWright.CompactBJRModel.B1](../PerronWright/Model/CompactBJR.lean#L93) | 存在实际 associated、紧致、自伴 L² 算子，算子范数为一。 |
| [PerronWright.CompactBJRModel.B2](../PerronWright/Model/CompactBJR.lean#L174) | 某个实际迭代核处处严格正。 |
| [PerronWright.CompactBJRModel.IsRegularCritical](../PerronWright/Model/CompactBJR.lean#L191) | `B1` 与 `B2`。 |
| [PerronWright.CompactBJRModel.QP](../PerronWright/Probability/ProjectiveKernel.lean#L82) | 核具有指定的 projective representation。 |
| [PerronWright.CompactBJRModel.perronFunction](../PerronWright/Model/PerronQuantities.lean#L22) | 正固定函数，归一化为 `∫φ dμ = 1`。 |
| [PerronWright.CompactBJRModel.alpha](../PerronWright/Model/PerronQuantities.lean#L92) | `∫φ² dμ`。 |
| [PerronWright.CompactBJRModel.beta](../PerronWright/Model/PerronQuantities.lean#L96) | `∫φ³ dμ`。 |

这里的 `QP` 是核的 **projective quadratic regularity**，不是 type 人数的准随机计数条件。其展开条件为：存在实系数 `aⱼ` 和连续函数 `fⱼ`，使 `κ(x,y) = Σⱼ aⱼ fⱼ(x)fⱼ(y)` 且 `Σⱼ |aⱼ| ‖fⱼ‖∞² < ∞`；精确定义见 [PerronWright.ProjectiveKernel.HasRepresentation](../PerronWright/Probability/ProjectiveKernel.lean#L47)。紧致型的本页概率定理额外要求 `QP`；与此相区分，[PerronWright.CompactPerronWrightTheorem.compactPerronWright_theorem](../PerronWright/Enumeration/CompactPerronWrightTheorem.lean#L232) 的枚举结论只要求 `IsRegularCritical`，不要求 `QP`。

## 3. 实际图源与 component count

两种图源都使用 edge hazard `z = t κ(xᵢ,xⱼ)/n`，给定 types 后不同边独立，边存在概率是 **`1 − exp(−z)`**，不是 `z`。有限型固定实际 assignment；紧致型先按 `μ` iid 采 types，再条件采边。

有限型中的 vertex types 是一个确定性的实际赋值序列 `xₙ : Fin n → S`，不在图概率律内重新采样。局部公式和十二条限度中的有限型分支要求存在同一个 `D ≥ 0`，使充分大的所有 n 及每个 type s 满足 `|fiberCount(xₙ,s) − n M.weight(s)| ≤ D`。这控制实际经验人数，而不是仅指定理想 type 比例；该条件是渐近定理的假设，不是 `FiniteIrreducibleTypedGraphLaw.law` 定义图源的必要条件。

| 完整 Lean 名称与位置 | 语义 |
| --- | --- |
| [PerronWright.IndependentEdges.edgeMass](../PerronWright/Probability/IndependentEdges.lean#L25) | 边存在/不存在的字面质量 `1−exp(−z)` / `exp(−z)`。 |
| [PerronWright.FiniteIrreducibleTypedGraphLaw.pairKernel](../PerronWright/Probability/FiniteIrreducibleTypedGraphLaw.lean#L27) | 固定 assignment 的实际 pair kernel。 |
| [PerronWright.FiniteIrreducibleTypedGraphLaw.hazard](../PerronWright/Probability/FiniteIrreducibleTypedGraphLaw.lean#L42) | `t κ/n`。 |
| [PerronWright.FiniteIrreducibleTypedGraphLaw.law](../PerronWright/Probability/FiniteIrreducibleTypedGraphLaw.lean#L52) | 固定 types 的实际图概率律。 |
| [PerronWright.AnnealedGraph.typeLaw](../PerronWright/Probability/AnnealedGraph.lean#L82) | iid type product law。 |
| [PerronWright.AnnealedGraph.hazard](../PerronWright/Probability/AnnealedGraph.lean#L86) | 紧致型的实际条件边 hazard。 |
| [PerronWright.AnnealedGraph.conditionalMass](../PerronWright/Probability/AnnealedGraph.lean#L95) | 固定 types 后的条件图质量。 |
| [PerronWright.AnnealedGraph.mass](../PerronWright/Probability/AnnealedGraph.lean#L128) | 对 types 积分后的图质量。 |
| [PerronWright.AnnealedGraph.law](../PerronWright/Probability/AnnealedGraph.lean#L166) | 实际 annealed 图律。 |
| [PerronWright.AnnealedTypedGraph.State](../PerronWright/Probability/AnnealedTypedGraph.lean#L31) | types 与边 assignment 的联合状态。 |
| [PerronWright.AnnealedTypedGraph.law](../PerronWright/Probability/AnnealedTypedGraph.lean#L39) | 实际 type/图联合律；经验 marked law 的源。 |
| [PerronWright.FiniteIrreducibleTypePlacementMultiplicity.fiberCount](../PerronWright/Probability/FiniteIrreducibleTypePlacementMultiplicity.lean#L97) | 实际 assignment 中每个 type 的顶点数。 |
| [PerronWright.ComponentCounts.blockSurplus](../PerronWright/Probability/ComponentCounts.lean#L27) | `edges + 1 − vertices`。 |
| [PerronWright.ComponentCounts.componentSize](../PerronWright/Probability/ComponentCounts.lean#L31) | 真正 connected component 的顶点数。 |
| [PerronWright.ComponentCounts.componentSurplus](../PerronWright/Probability/ComponentCounts.lean#L35) | 真正 connected component 的 surplus。 |
| [PerronWright.ComponentCounts.GoodComponentTuples](../PerronWright/Probability/ComponentCounts.lean#L46) | 有序、互不相同且 size/surplus 指定的实际 component tuples。 |
| [PerronWright.ComponentCounts.count](../PerronWright/Probability/ComponentCounts.lean#L60) | 上述 tuples 的基数；不是 graph-pattern surrogate。 |

以下是十二条收敛定理陈述中的实际 source laws：

| 完整 Lean 名称与位置 | 源律 |
| --- | --- |
| [PerronWright.FiniteIrreducibleComponentProcess.graphLaw](../PerronWright/Probability/FiniteIrreducibleComponentProcess.lean#L28) | 临界时间的有限型图律。 |
| [PerronWright.FiniteIrreducibleComponentProcess.unmarkedProcessLaw](../PerronWright/Probability/FiniteIrreducibleComponentProcess.lean#L38) | 有限型全局未标记。 |
| [PerronWright.FiniteIrreducibleComponentProcess.unmarkedWindowLaw](../PerronWright/Probability/FiniteIrreducibleComponentProcess.lean#L43) | 有限型窗口未标记。 |
| [PerronWright.ComponentWindowPointMeasures.unmarkedWindowLaw](../PerronWright/Probability/ComponentWindowPointMeasures.lean#L249) | 紧致型窗口未标记。 |
| [PerronWright.ComponentGlobalPointProcess.unmarkedProcessLaw](../PerronWright/Probability/ComponentGlobalPointProcess.lean#L218) | 紧致型全局未标记。 |
| [PerronWright.FiniteIrreducibleMarkedComponentProcess.markedWindowLaw](../PerronWright/Probability/FiniteIrreducibleMarkedComponentProcess.lean#L46) | 有限型实际经验标记窗口。 |
| [PerronWright.FiniteIrreducibleMarkedComponentProcess.markedProcessLaw](../PerronWright/Probability/FiniteIrreducibleMarkedComponentProcess.lean#L52) | 有限型实际经验标记全局。 |
| [PerronWright.ComponentWindowMarkedLaw.markedWindowLaw](../PerronWright/Probability/ComponentWindowMarkedLaw.lean#L77) | 紧致型实际经验标记窗口。 |
| [PerronWright.ComponentGlobalMarkedProcess.markedProcessLaw](../PerronWright/Probability/ComponentGlobalMarkedProcess.lean#L76) | 紧致型实际经验标记全局。 |

## 4. 局部缩放、密度与 factorial 测试

令 `q` 为有序 component 个数，`rᵢ` 为各槽 surplus，`xᵢ > 0` 为各槽缩放 size。局部公式中的期望是 `n^(2q/3) E[count]`。密度定义为

\[
F_{\alpha,\beta,\lambda}(s)
=\frac{\beta s^3}{6}-\frac{\alpha\lambda s^2}{2}
+\frac{\alpha^2\lambda^2s}{2\beta},\qquad
g_r(x)=\frac{w_r\beta^{(r-1)/2}}{\sqrt{2\pi}}x^{3r/2-5/2},
\]

\[
\rho_q(x,r)=\exp\!\left(-F_{\alpha,\beta,\lambda}\!\left(\sum_i x_i\right)\right)
\prod_i g_{r_i}(x_i).
\]

实际 Aldous/Brownian 阶乘密度是这里的 `α = β = 1` 特例。

| 完整 Lean 名称与位置 | 语义 |
| --- | --- |
| [PerronWright.CriticalScaling.time](../PerronWright/Probability/CriticalScaling.lean#L24) | `max(1+λ n^(−1/3),0)`；小 n 的 clipping 保证图律有定义。 |
| [PerronWright.CriticalScaling.size](../PerronWright/Probability/CriticalScaling.lean#L49) | 字面 floor `⌊x n^(2/3)⌋₊`。 |
| [PerronWright.FiniteIrreducibleCriticalPrefactorScaling.rawTime](../PerronWright/Probability/FiniteIrreducibleCriticalPrefactorScaling.lean#L19) | 论文 raw time。 |
| [PerronWright.FiniteIrreducibleCriticalPrefactorScaling.normalizedSize](../PerronWright/Probability/FiniteIrreducibleCriticalPrefactorScaling.lean#L22) | `k/n^(2/3)`。 |
| [PerronWright.FiniteIrreducibleLocalMainIdentity.scaledFactorialExpectation](../PerronWright/Probability/FiniteIrreducibleLocalMainIdentity.lean#L34) | 固定 types 的 scaled 实际 factorial expectation。 |
| [PerronWright.CompactAnnealedFactorialLocal.localExpectation](../PerronWright/Probability/CompactAnnealedFactorialLocal.lean#L27) | Annealed 的 floor scaled 实际 factorial expectation。 |
| [PerronWright.FactorialDensity.sizeWindow](../PerronWright/Probability/FactorialWindowMass.lean#L21) | q 维 size 闭窗口。 |
| [PerronWright.PerronWrightFormulaMainTerm.wrightConstant](../PerronWright/Enumeration/PerronWrightFormulaMainTerm.lean#L25) | 各 surplus 的 Wright 常数 `wᵣ`。 |
| [PerronWright.FactorialDensity.criticalExponent](../PerronWright/Probability/FactorialDensity.lean#L19) | 上述 `F`。 |
| [PerronWright.FactorialDensity.sizeFactor](../PerronWright/Probability/FactorialDensity.lean#L24) | 上述 `gᵣ`。 |
| [PerronWright.FactorialDensity.density](../PerronWright/Probability/FactorialDensity.lean#L29) | 上述有序 q-point density。 |
| [PerronWright.FinitePointMeasureFactorialMeasure.factorialMeasure](../PerronWright/Probability/FinitePointMeasureFactorialMeasure.lean#L74) | 实际点测度的内在有序不同原子 factorial measure。 |
| [PerronWright.FinitePointMeasureFactorialKernel.rectangleTest](../PerronWright/Probability/FinitePointMeasureFactorialKernel.lean#L32) | 各槽 rectangle restriction 与任意耦合测试的积分。 |
| [PerronWright.BrownianExcursionRectangleFactorials.cells](../PerronWright/Probability/BrownianExcursionRectangleFactorials.lean#L32) | 各槽 `Icc(aᵢ,bᵢ) × {rᵢ}`。 |
| [PerronWright.BrownianExcursionRectangleFactorials.windowSet](../PerronWright/Probability/BrownianExcursionRectangleFactorials.lean#L39) | 各槽 cells 的 union。 |
| [PerronWright.BrownianExcursionFactorialTests.factorialTest](../PerronWright/Probability/BrownianExcursionFactorialTests.lean#L34) | 实际窗口点测度上的内在 factorial test。 |
| [PerronWright.BrownianExcursionDeletionTupleSource.sourceSum](../PerronWright/Probability/BrownianExcursionDeletionTupleSource.lean#L31) | 完整面积 Poisson 权重的有序 excursion source sum。 |
| [PerronWright.ComponentWindowMixedFactorials.sizeSurplusCells](../PerronWright/Probability/ComponentWindowMixedFactorials.lean#L146) | `Jᵢ × Sᵢ` size/surplus cells。 |
| [PerronWright.FactorialCountDeterminacy.factorialPolynomial](../PerronWright/Probability/FactorialCountDeterminacy.lean#L101) | 各 cell count 的 descending factorial 乘积。 |
| [PerronWright.FactorialCountDeterminacy.factorialMoment](../PerronWright/Probability/FactorialCountDeterminacy.lean#L104) | 上述 polynomial 的期望。 |
| [PerronWright.BrownianActualArbitraryWindowCellMoments.mixedStatistic](../PerronWright/Probability/BrownianActualArbitraryWindowCellMoments.lean#L30) | 任意窗口的 mixed factorial count statistic。 |
| [PerronWright.BrownianActualArbitraryWindowCellMoments.cellCountLaw](../PerronWright/Probability/BrownianActualArbitraryWindowCellMoments.lean#L187) | 任意实际 Brownian 窗口的 cell-count 联合律。 |
| [PerronWright.CompactSizeCellFactorialLimits.cellMomentMass](../PerronWright/Probability/CompactSizeCellFactorialLimits.lean#L31) | 保留所有槽重数的字面 density 积分。 |

时间 clipping 与论文 raw time 的尾部一致性见 [PerronWright.CriticalScaling.time_eq_raw_eventually](../PerronWright/Probability/CriticalScaling.lean#L36)。

## 5. 点测度空间与拓扑

窗口点测度使用从 `FiniteMeasure` 继承的 **weak topology** 与其 Borel sigma algebra；全局 locally finite 点测度使用所有 compact-support 连续测试积分诱导的 **vague topology** 与其 Borel sigma algebra。主定理中的 `Tendsto` 则是这些点测度空间上概率律的弱收敛；不要把底层点测度拓扑和概率律收敛混为一层。

| 完整 Lean 名称与位置 | 语义 |
| --- | --- |
| [PerronWright.FinitePointMeasureCompact.IsPointMeasure](../PerronWright/Probability/FinitePointMeasureCompact.lean#L28) | 有限整数 Dirac 和，包含重数与零测度。 |
| [PerronWright.FinitePointMeasureCompact.PointMeasure](../PerronWright/Probability/FinitePointMeasureCompact.lean#L33) | 实际有限点测度空间。 |
| [PerronWright.FinitePointMeasureCompact.size](../PerronWright/Probability/FinitePointMeasureCompact.lean#L97) | 点数，计重数。 |
| [PerronWright.FinitePointMeasureCompact.count](../PerronWright/Probability/FinitePointMeasureCompact.lean#L112) | 集合内点数。 |
| [PerronWright.FinitePointMeasureCompact.SurplusWindow](../PerronWright/Probability/FinitePointMeasureCompact.lean#L250) | `Icc a b × Fin(R+1)`。 |
| [PerronWright.LocallyFinitePointMeasureVague.IsLocallyFinitePointMeasure](../PerronWright/Probability/LocallyFinitePointMeasureVague.lean#L25) | 局部有限，且每个 compact restriction 为有限整数 Dirac 和。 |
| [PerronWright.LocallyFinitePointMeasureVague.LocalPointMeasure](../PerronWright/Probability/LocallyFinitePointMeasureVague.lean#L29) | 实际全局 locally finite 点测度空间。 |
| [PerronWright.LocallyFinitePointMeasureVague.testEncoding](../PerronWright/Probability/LocallyFinitePointMeasureVague.lean#L42) | 所有 `C_c` 测试积分。 |
| [PerronWright.ComponentGlobalPointProcess.PositiveSizeSurplus](../PerronWright/Probability/ComponentGlobalPointProcess.lean#L25) | `(0,∞) × ℕ`。 |
| [PerronWright.ComponentWindowPointMeasures.windowEmbedding](../PerronWright/Probability/ComponentWindowPointMeasures.lean#L31) | 窗口坐标到 ambient size/surplus 的 embedding。 |
| [PerronWright.ComponentWindowPointMeasures.windowPointMeasure](../PerronWright/Probability/ComponentWindowPointMeasures.lean#L78) | 窗口内实际 components 的整数点测度。 |
| [PerronWright.ComponentGlobalPointProcess.unmarkedProcess](../PerronWright/Probability/ComponentGlobalPointProcess.lean#L58) | 所有实际 components 的正 size/surplus 点测度。 |

拓扑和 Borel instances 的源码位置：[有限 weak topology](../PerronWright/Probability/FinitePointMeasureCompact.lean#L61)、[有限 weak-Borel](../PerronWright/Probability/FinitePointMeasureCompact.lean#L66)、[全局 vague topology](../PerronWright/Probability/LocallyFinitePointMeasureVague.lean#L45)、[全局 vague-Borel](../PerronWright/Probability/LocallyFinitePointMeasureVague.lean#L48)。

## 6. 真实 Brownian 来源与 Aldous law

目标律不是仅凭密度定义的候选过程：它由实际连续 Brownian whole-path law 构造 `B(t)+λt−t²/2`，按 running minimum 反射，取完整正 excursions，并给每个 excursion 附 Poisson surplus，其条件 rate 是完整 excursion 面积。Poisson marks **给定路径后独立**，不是与路径无条件独立。全局点过程 law 是这个实际 path/mark 联合律的 pushforward。

| 完整 Lean 名称与位置 | 语义 |
| --- | --- |
| [PerronWright.BrownianPathLaw.Path](../PerronWright/Probability/BrownianPathLaw.lean#L32) | 连续 whole-path 空间 `C(ℝ≥0,ℝ)`。 |
| [PerronWright.BrownianPathLaw.pathLaw](../PerronWright/Probability/BrownianPathLaw.lean#L111) | 真实 Brownian whole-path law。 |
| [PerronWright.BrownianPathReflectionLaw.reflectionPath](../PerronWright/Probability/BrownianPathReflectionLaw.lean#L30) | 减去 running minimum。 |
| [PerronWright.BrownianPathReflectionLaw.driftPath](../PerronWright/Probability/BrownianPathReflectionLaw.lean#L33) | `B(t)+λt−t²/2`。 |
| [PerronWright.BrownianPathReflectionLaw.driftedReflectionPath](../PerronWright/Probability/BrownianPathReflectionLaw.lean#L36) | 上述 drifted path 的反射。 |
| [PerronWright.FullHorizonExcursionComponents.component](../PerronWright/Probability/FullHorizonExcursionComponents.lean#L27) | 正 excursion 的 connected component。 |
| [PerronWright.FullHorizonExcursionComponents.leftEndpoint](../PerronWright/Probability/FullHorizonExcursionComponents.lean#L117) | 完整 excursion 左端点。 |
| [PerronWright.FullHorizonExcursionComponents.rightEndpoint](../PerronWright/Probability/FullHorizonExcursionComponents.lean#L120) | 完整 excursion 右端点。 |
| [PerronWright.FullHorizonExcursionComponents.length](../PerronWright/Probability/FullHorizonExcursionComponents.lean#L123) | 完整而非截断 excursion 长度。 |
| [PerronWright.FullHorizonExcursionSection.Representative](../PerronWright/Probability/FullHorizonExcursionSection.lean#L75) | 每个 excursion 的不重复 rational representative。 |
| [PerronWright.BrownianFullHorizonExcursionAreas.excursionArea](../PerronWright/Probability/BrownianFullHorizonExcursionAreas.lean#L51) | 完整而非截断 excursion 面积。 |
| [PerronWright.BrownianFullHorizonPoissonMarks.naturalRates](../PerronWright/Probability/BrownianFullHorizonPoissonMarks.lean#L28) | 以完整面积为条件 rate。 |
| [PerronWright.BrownianFullHorizonPoissonMarks.markLaw](../PerronWright/Probability/BrownianFullHorizonPoissonMarks.lean#L78) | 给定路径的条件 Poisson mark law。 |
| [PerronWright.BrownianFullHorizonPoissonMarks.pathJointLaw](../PerronWright/Probability/BrownianFullHorizonPoissonMarks.lean#L174) | 实际 path 与 surplus marks 联合律。 |
| [PerronWright.BrownianExcursionAtomicMeasure.measure](../PerronWright/Probability/BrownianExcursionAtomicMeasure.lean#L51) | 实际 excursion 原子测度。 |
| [PerronWright.BrownianExcursionAtomicMeasure.process](../PerronWright/Probability/BrownianExcursionAtomicMeasure.lean#L141) | 实际全局 locally finite excursion 点测度。 |
| [PerronWright.BrownianExcursionPointProcessLaw.law](../PerronWright/Probability/BrownianExcursionPointProcessLaw.lean#L45) | 实际 Aldous global probability law。 |
| [PerronWright.BrownianExcursionPointProcessLaw.windowLaw](../PerronWright/Probability/BrownianExcursionPointProcessLaw.lean#L53) | Canonical chart 的实际 Brownian law。 |
| [PerronWright.BrownianArbitraryWindowLaw.pointMeasure](../PerronWright/Probability/BrownianArbitraryWindowLaw.lean#L150) | 任意正 size 闭窗口的实际 Brownian 点测度。 |
| [PerronWright.BrownianArbitraryWindowLaw.law](../PerronWright/Probability/BrownianArbitraryWindowLaw.lean#L183) | 任意正 size 闭窗口的实际 Brownian probability law。 |
| [PerronWright.BrownianExcursionCompactWindows.law](../PerronWright/Probability/BrownianExcursionCompactWindows.lean#L72) | 任意 compact 集窗口的实际 law；密度定理使用的对象。 |

## 7. 真实经验标记、Perron 标记与 TV 区别

一个实际 component `C` 的 mark 是概率测度 `|C|⁻¹ Σ_{v∈C} δ_{xᵥ}`，不是预先指定的 profile。极限中的确定性 Perron mark 是 `φ dμ`；有限型为 `Σₐ μₐφₐ δₐ`。它一般不等于原始采样律 `μ`。`canonicalPerronMarkedLaw` / `canonicalGlobalMarkedLaw` 将这个同一 Perron 概率测度附到未标记目标的每个原子上。

本页十二条 finite/compact 定理中的 marks 使用真实概率测度的 **weak topology**，由 `WeakMark` 选择其 Borel structure；这不是可数型局部 TV 标记结论中的 total-variation topology。不能将本页 marked global law 擅自解释为全局 TV-product 标记律。

| 完整 Lean 名称与位置 | 语义 |
| --- | --- |
| [PerronWright.EmpiricalTypeMarks.empiricalMeasure](../PerronWright/Probability/EmpiricalTypeMarks.lean#L31) | Block 的实际经验测度。 |
| [PerronWright.EmpiricalTypeMarks.empiricalProbability](../PerronWright/Probability/EmpiricalTypeMarks.lean#L45) | 非空 block 的经验 probability measure。 |
| [PerronWright.EmpiricalTypeMarks.componentMark](../PerronWright/Probability/EmpiricalTypeMarks.lean#L75) | 实际 component 的经验 mark。 |
| [PerronWright.EmpiricalTypeMarks.perronMark](../PerronWright/Probability/EmpiricalTypeMarks.lean#L118) | 紧致型 Perron probability mark。 |
| [PerronWright.WeakProbabilityMarks.WeakMark](../PerronWright/Probability/WeakProbabilityMarks.lean#L17) | 值仍是 `ProbabilityMeasure S` 的 weak-Borel wrapper。 |
| [PerronWright.WeakProbabilityMarks.homeomorph](../PerronWright/Probability/WeakProbabilityMarks.lean#L27) | 与 probability measure 的真实 weak topology 的 homeomorphism。 |
| [PerronWright.FiniteIrreducibleConnectedTypeLaw.perronLaw](../PerronWright/Probability/FiniteIrreducibleConnectedTypeLaw.lean#L43) | 有限型 Perron probability law。 |
| [PerronWright.FiniteIrreducibleMarkedComponentProcess.perronWeakMark](../PerronWright/Probability/FiniteIrreducibleMarkedComponentProcess.lean#L31) | 有限型 Perron weak mark。 |
| [PerronWright.ComponentWindowMarkedTransfer.perronWeakMark](../PerronWright/Probability/ComponentWindowMarkedTransfer.lean#L28) | 紧致型 Perron weak mark。 |
| [PerronWright.ComponentWindowMarkedLaw.MarkedWindow](../PerronWright/Probability/ComponentWindowMarkedLaw.lean#L29) | `SurplusWindow × WeakMark`。 |
| [PerronWright.ComponentWindowMarkedLaw.markedWindowPointMeasure](../PerronWright/Probability/ComponentWindowMarkedLaw.lean#L40) | 真正经验 marked window 点测度。 |
| [PerronWright.ComponentGlobalMarkedProcess.MarkedPositiveSizeSurplus](../PerronWright/Probability/ComponentGlobalMarkedProcess.lean#L33) | `PositiveSizeSurplus × WeakMark`。 |
| [PerronWright.ComponentGlobalMarkedProcess.markedProcess](../PerronWright/Probability/ComponentGlobalMarkedProcess.lean#L45) | 真正经验 marked global 点测度。 |
| [PerronWright.GlobalPointMeasureMarking.constantMark](../PerronWright/Probability/GlobalPointMeasureMarking.lean#L53) | 给每个原子附同一概率 mark 的点测度 pushforward。 |
| [PerronWright.FiniteIrreducibleMarkedWindowConvergence.canonicalPerronMarkedLaw](../PerronWright/Probability/FiniteIrreducibleMarkedWindowConvergence.lean#L26) | 有限型 Perron-marked window 目标律。 |
| [PerronWright.ComponentWindowMarkedConvergence.canonicalPerronMarkedLaw](../PerronWright/Probability/ComponentWindowMarkedConvergence.lean#L27) | 紧致型 Perron-marked window 目标律。 |
| [PerronWright.FiniteIrreducibleMarkedGlobalTests.canonicalGlobalMarkedLaw](../PerronWright/Probability/FiniteIrreducibleMarkedGlobalTests.lean#L33) | 有限型 Perron-marked global 目标律。 |
| [PerronWright.GlobalPointMeasureMarking.canonicalGlobalMarkedLaw](../PerronWright/Probability/GlobalPointMeasureMarking.lean#L78) | 紧致型 Perron-marked global 目标律。 |

## 8. 星号与 inverse Brownian 归一化

论文星号变换只把 size 乘 `c = β^(1/3)`，保留 surplus 和实际经验 mark。目标的 Brownian 参数是 `λ⋆ = α β^(−2/3) λ`。未星号全局律的目标是参数 `λ⋆` 的真实 Brownian law 经 size 乘 `c⁻¹` 后的律；星号全局律的目标直接是该真实 Brownian law。未星号窗口目标先取 Brownian 的 `[ca,cb]` 窗口，再以 size 乘 `c⁻¹` 映回 `[a,b]`。

| 完整 Lean 名称与位置 | 语义 |
| --- | --- |
| [PerronWright.ComponentPointProcesses.sizeScale](../PerronWright/Probability/PointProcessNormalization.lean#L37) | 紧致型 `β^(1/3)`。 |
| [PerronWright.ComponentPointProcesses.aldousParameter](../PerronWright/Probability/PointProcessNormalization.lean#L45) | 紧致型 `αβ^(−2/3)λ`。 |
| [PerronWright.FiniteIrreduciblePointProcessNormalization.sizeScale](../PerronWright/Probability/FiniteIrreduciblePointProcessNormalization.lean#L26) | 有限型 `β^(1/3)`。 |
| [PerronWright.FiniteIrreduciblePointProcessNormalization.paperParameter](../PerronWright/Probability/FiniteIrreduciblePointProcessNormalization.lean#L41) | 有限型 `αβ^(−2/3)λ`。 |
| [PerronWright.GlobalPointSizeRescaling.positiveSizeScale](../PerronWright/Probability/GlobalPointSizeRescaling.lean#L25) | 正 size 基空间上的 size dilation homeomorphism。 |
| [PerronWright.GlobalPointSizeRescaling.scalePoint](../PerronWright/Probability/GlobalPointSizeRescaling.lean#L53) | 全局点测度的实际 dilation pushforward。 |
| [PerronWright.GlobalPointSizeRescaling.starredProcessLaw](../PerronWright/Probability/GlobalPointSizeRescaling.lean#L112) | 紧致型星号未标记全局 source law。 |
| [PerronWright.GlobalMarkedPointSizeRescaling.scaleMarkedPoint](../PerronWright/Probability/GlobalMarkedPointSizeRescaling.lean#L52) | 保留 mark 的全局 size dilation。 |
| [PerronWright.GlobalMarkedPointSizeRescaling.starredMarkedProcessLaw](../PerronWright/Probability/GlobalMarkedPointSizeRescaling.lean#L156) | 紧致型星号经验标记全局 source law。 |
| [PerronWright.FiniteIrreducibleGlobalSizeRescaling.starredProcessLaw](../PerronWright/Probability/FiniteIrreducibleGlobalSizeRescaling.lean#L77) | 有限型星号未标记全局 source law。 |
| [PerronWright.FiniteIrreducibleGlobalMarkedSizeRescaling.starredMarkedProcessLaw](../PerronWright/Probability/FiniteIrreducibleGlobalMarkedSizeRescaling.lean#L148) | 有限型星号经验标记全局 source law。 |
| [PerronWright.BrownianInverseSizeLaw.inverseScaledLaw](../PerronWright/Probability/BrownianInverseSizeLaw.lean#L41) | 实际 Brownian global law 的 inverse-size dilation。 |
| [PerronWright.BrownianInverseWindowLaw.law](../PerronWright/Probability/BrownianInverseWindowLaw.lean#L24) | 实际 arbitrary Brownian window law 的 inverse-size dilation。 |

上述十二个入口已有逐条 `#print axioms` 的源码入口：[ModelActualBrownianLimitsAudit.lean](../PerronWright/Probability/ModelActualBrownianLimitsAudit.lean#L3)。`#print axioms` 打印逻辑公理依赖，不等于完整的中间定理调用图；一键验证入口应明确区分两者。
