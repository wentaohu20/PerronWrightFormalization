# 可数类型：主定理、定义与准确范围

本页索引可数临界实现及不做谱归一化时的两个主结果。所有链接指向本仓库的 Lean 源码；这里只解释声明的含义，不记录运行测试状态。

## 公共主定理入口

完整声明名：

```text
PerronWright.CountableActualBrownianLimits.exists_actual_growing_Brownian_global_and_TV_window_limits
```

位置：[CountableActualBrownianLimits.lean，第 90 行](../PerronWright/Probability/CountableActualBrownianLimits.lean#L90)。两个结果由这个联合定理给出，不是分别选择两套整数实现。

模型输入是 `M : CountableKernel` 与 `hM : M.IsRegularCritical`，以及 `0 < lower`、`lower ≤ M.kernel s t` 的下界见证。该见证已经包含在正则临界性中，并非额外模型假设。定理前的 [`omit level hlocal in`](../PerronWright/Probability/CountableActualBrownianLimits.lean#L86) 表明：支撑序列由结论构造，局部极限估计不是外部假设。

### 同一个最外层 `∃ level` 覆盖什么

| 联合结论 | 主定理中的位置 |
| --- | --- |
| `level` 单调、趋于无穷、`level N ≤ N`；每个 `N` 的人数之和恰为 `N`，且 `N>0` 时各保留类型人数严格为正 | [第 91 行](../PerronWright/Probability/CountableActualBrownianLimits.lean#L91) |
| 实际经验概率测度在原子绝对变差中趋于原始 `μ`；`N^(1/3)` 乘各保留类型经验比例的最小值趋于无穷 | [第 97 行](../PerronWright/Probability/CountableActualBrownianLimits.lean#L97) |
| 谱归一化图源的局部阶乘期望趋于原始 `α,β` 的密度；对每个固定阶数、surplus 上界、正大小窗口和有界临界参数区间一致 | [第 104 行](../PerronWright/Probability/CountableActualBrownianLimits.lean#L104) |
| 在实际经验谱漂移假设下，同一原始图源的局部期望趋于参数 `λ+θ` 的密度 | [第 110 行](../PerronWright/Probability/CountableActualBrownianLimits.lean#L110) |
| 谱归一化 starred 全局无标记图法则趋于实际 Brownian 全 excursion 法则 | [第 120 行](../PerronWright/Probability/CountableActualBrownianLimits.lean#L120) |
| 谱漂移假设下，同一原始 starred 全局无标记图法则趋于相应 Brownian 法则 | [第 124 行](../PerronWright/Probability/CountableActualBrownianLimits.lean#L124) |
| 每个正闭大小–有界 surplus 窗口上的谱归一化 starred 无标记法则与实际经验 TV 标记法则收敛 | [第 131 行](../PerronWright/Probability/CountableActualBrownianLimits.lean#L131) |
| 谱漂移假设下，同一原始 starred 无标记及经验 TV 标记窗口法则收敛 | [第 139 行](../PerronWright/Probability/CountableActualBrownianLimits.lean#L139) |
| 谱归一化模型在窗口内的标记距离总和期望及坏标记概率趋于零 | [第 150 行](../PerronWright/Probability/CountableActualBrownianLimits.lean#L150) |
| 谱漂移假设下，原始模型的相应标记距离期望及坏标记概率趋于零 | [第 155 行](../PerronWright/Probability/CountableActualBrownianLimits.lean#L155) |

`∃ level` 在所有 `λ`、`θ`、阶数及窗口参数之前。因此这些结论使用同一个顶点类型赋值、同一个正整数人数构造和同一个穷尽支撑，而不是逐参数重新选取实现。

### 索引、谱漂移与 starred 参数

图序列的 Lean 索引为 `n`，实际顶点数为 `N = n+1`。支撑是 `{0,…,level N}`，实际谱半径记为 `σ_n = M.empiricalSpectralRadius level n`。

原始图分支的前提严格是：

```text
(n+1)^(1/3) * (M.empiricalSpectralRadius level n - 1) → θ.
```

在该前提下，原始局部密度参数为 `λ+θ`。全局及窗口 starred 极限的实际 Brownian 参数为：

```text
谱归一化： α * β^(-2/3) * λ
原始图源： α * β^(-2/3) * (λ+θ)
```

这里的 `θ` 在比例因子内部。原始谱漂移条件是针对实际经验核的条件，不是针对另选的近似谱根；主定理也没有声称仅靠正则临界性自动得到任意 `θ` 或零漂移。零漂移结果是上述条件分支的 `θ=0` 特例。

starred 大小坐标用原始可数模型的 `β^(1/3)` 乘 `|C|/N^(2/3)`，surplus 与实际经验类型标记不变；不是用每个经验有限模型自身的 `β_n` 来替换原始 `β`。

### 拓扑和窗口范围

- 全局结论只有**无标记**法则：底空间为 `(0,∞) × ℕ`，局部有限整数点测度带 vague 拓扑，再讨论其概率法则的弱收敛。
- 标记结论是局部窗口上的概率法则弱收敛。窗口是闭集 `[a,b] × {0,…,R}`，条件为 `0<a≤b`，包含两端点；公共主定理没有要求用户额外提供边界零质量证明。
- 标记底空间是该窗口与 `VariationMark` 的乘积；后者的距离是 `Σ_s |p{s}-q{s}|`，即通常采用 `sup_A |p(A)-q(A)|` 的 TV 约定的两倍。
- “TV 标记极限”表示使用这个总变差标记拓扑，不表示整个点过程概率法则之间按总变差收敛，也不宣称全局 TV-product 标记点过程极限。
- 目标标记法则由无标记 Brownian 窗口法则添加原始 Perron 常标记而成；有限图源仍然使用每个实际组件自身的经验标记。

## 一、模型假设与原始 Perron 量

| 含义 | 完整 Lean 声明名与位置 |
| --- | --- |
| 类型空间 `ℕ`；每个类型原子为正的概率测度 `μ`；有界、对称、非负核 `κ` | [`PerronWright.CountableKernel`](../PerronWright/Model/CountableKernel.lean#L19) |
| 原始 `L²(μ)` 空间 | [`PerronWright.CountableKernel.L2`](../PerronWright/Kernel/CountableIntegral.lean#L21) |
| 积分核点值作用 `∫ κ(a,b)v(b) dμ(b)` | [`PerronWright.CountableKernel.pointwiseAction`](../PerronWright/Kernel/CountableIntegral.lean#L54) |
| 该作用对应的连续线性算子 | [`PerronWright.CountableKernel.actionCLM`](../PerronWright/Kernel/CountableIntegral.lean#L106) |
| 临界性：原始算子的谱半径等于一 | [`PerronWright.CountableKernel.IsCritical`](../PerronWright/Kernel/CountablePerron.lean#L19) |
| 正则临界性：临界性加核的统一严格正下界 | [`PerronWright.CountableKernel.IsRegularCritical`](../PerronWright/Model/CountablePerronQuantities.lean#L18) |
| 规范化正 Perron 固定向量的存在唯一性 | [`PerronWright.CountableKernel.IsRegularCritical.existsUnique_normalized_positive_fixed`](../PerronWright/Model/CountablePerronQuantities.lean#L21) |
| 从存在唯一性定理选出的规范化正向量 `u` | [`PerronWright.CountableKernel.perronVector`](../PerronWright/Model/CountablePerronQuantities.lean#L27) |
| `u>0` | [`PerronWright.CountableKernel.perronVector_pos`](../PerronWright/Model/CountablePerronQuantities.lean#L30) |
| `Ku=u` | [`PerronWright.CountableKernel.perronVector_fixed`](../PerronWright/Model/CountablePerronQuantities.lean#L34) |
| `∫u dμ=1` | [`PerronWright.CountableKernel.perronVector_integral`](../PerronWright/Model/CountablePerronQuantities.lean#L38) |
| 以 `u` 为密度的 Perron 概率测度 `u·μ` | [`PerronWright.CountableKernel.perronLaw`](../PerronWright/Model/CountablePerronQuantities.lean#L52) |
| 二次尺度 `α=∫u² dμ` | [`PerronWright.CountableKernel.alpha`](../PerronWright/Model/CountablePerronQuantities.lean#L92) |
| 三次尺度 `β=∫u³ dμ` | [`PerronWright.CountableKernel.beta`](../PerronWright/Model/CountablePerronQuantities.lean#L95) |

## 二、增长支撑、整数人数与经验谱根

人数构造先在初始支撑 `{0,…,m}` 上规范化原始权重，然后取整；全部取整余数放在类型 `0`。实际顶点赋值实现这些人数，不仅仅给出一组实数权重。主定理在 `N>0` 时断言严格正人数与经验概率性质；`N=0` 时不要求经验测度是概率测度。

| 含义 | 完整 Lean 声明名与位置 |
| --- | --- |
| 原始原子权重 `w(a)=μ.real {a}` | [`PerronWright.CountableTypeRealization.weights`](../PerronWright/Probability/CountableTypeRealization.lean#L28) |
| 截断质量 `Σ_{a≤m} w(a)` | [`PerronWright.GrowingTypeCounts.mass`](../PerronWright/Probability/GrowingTypeCounts.lean#L23) |
| 规范化截断分布 `w(a)/mass(w,m)` | [`PerronWright.GrowingTypeCounts.truncatedLaw`](../PerronWright/Probability/GrowingTypeCounts.lean#L46) |
| 有限类型取整人数及余数处理 | [`PerronWright.FiniteTypeCounts.counts`](../PerronWright/Model/FiniteTypeCounts.lean#L32) |
| 和恰为 `N` 的截断整数人数 | [`PerronWright.GrowingTypeCounts.truncatedCounts`](../PerronWright/Probability/GrowingTypeCounts.lean#L57) |
| 这些人数除以 `N` 得到的有限经验频率 | [`PerronWright.GrowingTypeCounts.empiricalLaw`](../PerronWright/Probability/GrowingTypeCounts.lean#L60) |
| 支撑 `{0,…,level N}` | [`PerronWright.GrowingTypeCounts.support`](../PerronWright/Probability/GrowingTypeCounts.lean#L137) |
| 每个实际顶点的自然数类型 | [`PerronWright.CountableTypeRealization.vertexTypes`](../PerronWright/Probability/CountableTypeRealization.lean#L30) |
| 顶点类型的实际经验测度 | [`PerronWright.CountableTypeRealization.empiricalMeasure`](../PerronWright/Probability/CountableTypeRealization.lean#L65) |
| 图索引 `n` 对应 `N=n+1` 时的经验原子权重 | [`PerronWright.CountableKernel.empiricalWeights`](../PerronWright/Kernel/CountableApproximationEmpirical.lean#L33) |
| 经验权重对应的实际算子 | [`PerronWright.CountableKernel.empiricalOperator`](../PerronWright/Kernel/CountableApproximationEmpirical.lean#L51) |
| 该算子的经验谱半径 `σ_n` | [`PerronWright.CountableKernel.empiricalSpectralRadius`](../PerronWright/Kernel/CountableApproximationEmpirical.lean#L55) |
| 加权积分算子谱半径的实值构造 | [`PerronWright.CountableKernel.weightedSpectralRadius`](../PerronWright/Kernel/CountableApproximationSpectral.lean#L69) |

## 三、规范化与原始独立边图源

令 `N=n+1`、`t_N=max(1+λN^(-1/3),0)`，并按上面的整数实现赋予顶点类型。对一条顶点类型为 `s,t` 的边：

```text
谱归一化 hazard： z = t_N * κ(s,t) / (N * σ_n)
原始图 hazard：   z = t_N * κ(s,t) / N
实际边概率：      1 - exp(-z)
```

这里 `z` 是 hazard，不是直接当作边概率。图法则是所有边的实际独立联合分布。有效参数把整个原始图法则精确改写为规范化法则，不仅改写某条边的边缘分布。

| 含义 | 完整 Lean 声明名与位置 |
| --- | --- |
| 临界时间 `t_N`；截断只用于避免小图尺寸的负时间 | [`PerronWright.CriticalScaling.time`](../PerronWright/Probability/CriticalScaling.lean#L24) |
| 给定 hazard 的单边 Boolean 概率质量 | [`PerronWright.IndependentEdges.edgeMass`](../PerronWright/Probability/IndependentEdges.lean#L25) |
| 实际带标签独立边图法则 | [`PerronWright.FixedTypeGraph.law`](../PerronWright/Probability/FixedTypeGraph.lean#L31) |
| 谱归一化 hazards | [`PerronWright.CountableKernel.empiricalNormalizedHazards`](../PerronWright/Probability/CountableEmpiricalGraphLaw.lean#L25) |
| 谱归一化实际图法则 | [`PerronWright.CountableKernel.empiricalNormalizedGraphLaw`](../PerronWright/Probability/CountableEmpiricalGraphLaw.lean#L41) |
| 原始 hazards | [`PerronWright.CountableKernel.empiricalUnnormalizedHazards`](../PerronWright/Probability/CountableEmpiricalGraphLaw.lean#L66) |
| 原始实际图法则 | [`PerronWright.CountableKernel.empiricalUnnormalizedGraphLaw`](../PerronWright/Probability/CountableEmpiricalGraphLaw.lean#L78) |
| 有效参数 `N^(1/3)((1+λN^(-1/3))σ-1)` | [`PerronWright.CriticalParameterDrift.effectiveParameter`](../PerronWright/Probability/CriticalParameterDrift.lean#L22) |
| 将实际经验谱根代入并按 `N=n+1` 重索引的有效参数 | [`PerronWright.CountableKernel.empiricalEffectiveParameter`](../PerronWright/Probability/CountableEmpiricalSpectralDrift.lean#L17) |
| 原始与规范化的完整图法则等式 | [`PerronWright.CountableKernel.empiricalUnnormalizedGraphLaw_eq_normalized`](../PerronWright/Probability/CountableEmpiricalGraphLaw.lean#L90) |

## 四、局部数值期望与目标阶乘密度

`q` 阶计数是有序且互不相同的实际连通组件元组数。第 `i` 个组件要求大小为 `⌊y_i N^(2/3)⌋₊`、surplus 为 `r_i`；surplus 按 `边数+1-顶点数` 定义。主定理中的局部量是 `N^(2q/3)` 乘这个计数的期望，分别在规范化或原始实际图法则下积分。

| 含义 | 完整 Lean 声明名与位置 |
| --- | --- |
| 实际组件大小 | [`PerronWright.ComponentCounts.componentSize`](../PerronWright/Probability/ComponentCounts.lean#L31) |
| 实际组件 surplus | [`PerronWright.ComponentCounts.componentSurplus`](../PerronWright/Probability/ComponentCounts.lean#L35) |
| 匹配大小与 surplus 的有序不同组件元组 | [`PerronWright.ComponentCounts.GoodComponentTuples`](../PerronWright/Probability/ComponentCounts.lean#L46) |
| 元组的实际阶乘计数 | [`PerronWright.ComponentCounts.count`](../PerronWright/Probability/ComponentCounts.lean#L60) |
| 真正取整的临界大小 | [`PerronWright.CriticalScaling.size`](../PerronWright/Probability/CriticalScaling.lean#L49) |
| 规范化局部期望 | [`PerronWright.CountableKernel.growingLocalExpectation`](../PerronWright/Probability/CountableFixedSupportGrowingSource.lean#L32) |
| 原始局部期望 | [`PerronWright.CountableKernel.growingUnnormalizedLocalExpectation`](../PerronWright/Probability/CountableUnnormalizedLocalTerminal.lean#L23) |
| surplus 索引的 Wright 常数 | [`PerronWright.PerronWrightFormulaMainTerm.wrightConstant`](../PerronWright/Enumeration/PerronWrightFormulaMainTerm.lean#L25) |
| 临界人口指数多项式 | [`PerronWright.FactorialDensity.criticalExponent`](../PerronWright/Probability/FactorialDensity.lean#L19) |
| 单个 surplus 对应的大小因子 | [`PerronWright.FactorialDensity.sizeFactor`](../PerronWright/Probability/FactorialDensity.lean#L24) |
| 目标有序 `q` 点阶乘密度 | [`PerronWright.FactorialDensity.density`](../PerronWright/Probability/FactorialDensity.lean#L29) |

## 五、全局点测度、闭窗口与 starred 法则

实际组件原子为 `(c * |C| / N^(2/3), surplus(C))`。每个组件贡献一个 Dirac 原子，保留重数；`c=1` 是未加 starred 尺度的坐标，`c=β^(1/3)` 是本定理的 starred 坐标。

| 含义 | 完整 Lean 声明名与位置 |
| --- | --- |
| 全局正大小–surplus 底空间 `(0,∞)×ℕ` | [`PerronWright.ComponentGlobalPointProcess.PositiveSizeSurplus`](../PerronWright/Probability/ComponentGlobalPointProcess.lean#L25) |
| 局部有限且紧集上为有限整数原子和的性质 | [`PerronWright.LocallyFinitePointMeasureVague.IsLocallyFinitePointMeasure`](../PerronWright/Probability/LocallyFinitePointMeasureVague.lean#L25) |
| 局部有限整数点测度空间 | [`PerronWright.LocallyFinitePointMeasureVague.LocalPointMeasure`](../PerronWright/Probability/LocallyFinitePointMeasureVague.lean#L29) |
| 用紧支撑连续测试函数积分定义 vague 拓扑 | [`PerronWright.LocallyFinitePointMeasureVague.testEncoding`](../PerronWright/Probability/LocallyFinitePointMeasureVague.lean#L42)；[拓扑实例](../PerronWright/Probability/LocallyFinitePointMeasureVague.lean#L45) |
| 有限整数点测度空间 | [`PerronWright.FinitePointMeasureCompact.PointMeasure`](../PerronWright/Probability/FinitePointMeasureCompact.lean#L33) |
| 有限点测度的弱拓扑 | [`PerronWright.FinitePointMeasureCompact` 中的 `TopologicalSpace` 实例](../PerronWright/Probability/FinitePointMeasureCompact.lean#L61) |
| 闭窗口 `[a,b]×{0,…,R}` | [`PerronWright.FinitePointMeasureCompact.SurplusWindow`](../PerronWright/Probability/FinitePointMeasureCompact.lean#L250) |
| 实际组件大小–surplus 原子 | [`PerronWright.ComponentWindowPointMeasures.componentAtom`](../PerronWright/Probability/ComponentWindowPointMeasures.lean#L49) |
| 落在闭窗口中的实际组件 | [`PerronWright.ComponentWindowPointMeasures.WindowComponent`](../PerronWright/Probability/ComponentWindowPointMeasures.lean#L58) |
| 每个选中组件一个原子的实际窗口点测度 | [`PerronWright.ComponentWindowPointMeasures.windowPointMeasure`](../PerronWright/Probability/ComponentWindowPointMeasures.lean#L78) |
| 原始可数三次尺度的 starred 倍率 `β^(1/3)` | [`PerronWright.CountableStarredGlobalSizeRescaling.sizeScale`](../PerronWright/Probability/CountableStarredGlobalSizeRescaling.lean#L26) |
| 规范化 starred 全局无标记法则 | [`PerronWright.CountableStarredGlobalSizeRescaling.normalizedStarredProcessLaw`](../PerronWright/Probability/CountableStarredGlobalSizeRescaling.lean#L32) |
| 原始 starred 全局无标记法则 | [`PerronWright.CountableStarredGlobalSizeRescaling.unnormalizedStarredProcessLaw`](../PerronWright/Probability/CountableStarredGlobalSizeRescaling.lean#L37) |
| 规范化 starred 无标记闭窗口法则 | [`PerronWright.CountableStarredTVWindowLaw.normalizedStarredWindowLaw`](../PerronWright/Probability/CountableStarredTVWindowLaw.lean#L30) |
| 规范化 starred 实际经验标记闭窗口法则 | [`PerronWright.CountableStarredTVWindowLaw.normalizedStarredMarkedWindowLaw`](../PerronWright/Probability/CountableStarredTVWindowLaw.lean#L36) |
| 原始 starred 无标记闭窗口法则 | [`PerronWright.CountableStarredTVWindowLaw.unnormalizedStarredWindowLaw`](../PerronWright/Probability/CountableStarredTVWindowLaw.lean#L43) |
| 原始 starred 实际经验标记闭窗口法则 | [`PerronWright.CountableStarredTVWindowLaw.unnormalizedStarredMarkedWindowLaw`](../PerronWright/Probability/CountableStarredTVWindowLaw.lean#L48) |
| 实际全 excursion、全面积 Poisson surplus 标记的 Brownian 全局法则 | [`PerronWright.BrownianExcursionPointProcessLaw.law`](../PerronWright/Probability/BrownianExcursionPointProcessLaw.lean#L45) |
| 实际 Brownian 全局过程在任意正闭窗口的法则 | [`PerronWright.BrownianArbitraryWindowLaw.law`](../PerronWright/Probability/BrownianArbitraryWindowLaw.lean#L183) |

## 六、实际经验 TV 标记与定量控制

一个组件的标记是该组件内部顶点自然数类型的实际经验概率，而不是人为赋予的 Perron 标记。极限才是把原始 Perron 概率作为常标记添加到每个 Brownian 组件原子上。

| 含义 | 完整 Lean 声明名与位置 |
| --- | --- |
| 任意顶点块的实际经验类型测度 | [`PerronWright.EmpiricalTypeMarks.empiricalMeasure`](../PerronWright/Probability/EmpiricalTypeMarks.lean#L31) |
| 实际组件的经验类型概率测度 | [`PerronWright.EmpiricalTypeMarks.componentMark`](../PerronWright/Probability/EmpiricalTypeMarks.lean#L75) |
| 以实际 `ℕ` 上概率测度为值的标记空间 | [`PerronWright.CountableVariationMarks.VariationMark`](../PerronWright/Probability/CountableVariationMarks.lean#L52) |
| 距离等于完整原子绝对变差和 | [`PerronWright.CountableVariationMarks.dist_eq_atomic_variation`](../PerronWright/Probability/CountableVariationMarks.lean#L72) |
| 完备性 | [`PerronWright.CountableVariationMarks.variationMarkComplete`](../PerronWright/Probability/CountableVariationTopology.lean#L56) |
| Polish 标记空间 | [`PerronWright.CountableVariationMarks.variationMarkPolish`](../PerronWright/Probability/CountableVariationTopology.lean#L84) |
| 原始 Perron 概率 `u·μ` 对应的 TV 标记 | [`PerronWright.CountablePerronMarkConvergence.perronMark`](../PerronWright/Probability/CountablePerronMarkConvergence.lean#L19) |
| 闭窗口与 TV 标记空间的乘积 | [`PerronWright.CountableComponentWindowLaw.MarkedWindow`](../PerronWright/Probability/CountableComponentWindowLaw.lean#L26) |
| 未加 starred 尺度的实际经验标记窗口点测度 | [`PerronWright.CountableComponentWindowLaw.markedWindowPointMeasure`](../PerronWright/Probability/CountableComponentWindowLaw.lean#L28) |
| 规范化实际图法则推前得到的经验标记窗口法则 | [`PerronWright.CountableKernel.empiricalMarkedWindowLaw`](../PerronWright/Probability/CountableComponentWindowLaw.lean#L98) |
| 原始实际图法则推前得到的经验标记窗口法则 | [`PerronWright.CountableKernel.empiricalUnnormalizedMarkedWindowLaw`](../PerronWright/Probability/CountableComponentWindowLaw.lean#L144) |
| starred 大小缩放后仍保留原经验标记的组件原子 | [`PerronWright.CountableTVWindowSizeRescaling.scaledMarkedWindowAtom`](../PerronWright/Probability/CountableTVWindowSizeRescaling.lean#L26) |
| starred 实际经验标记窗口点测度 | [`PerronWright.CountableTVWindowSizeRescaling.scaledMarkedWindowPointMeasure`](../PerronWright/Probability/CountableTVWindowSizeRescaling.lean#L35) |
| 将常 Perron 标记添加到无标记窗口法则上的推前 | [`PerronWright.CountableTVWindowConvergence.canonicalMarkedWindowLaw`](../PerronWright/Probability/CountableTVWindowConvergence.lean#L26) |
| 窗口内所有组件标记距离的总和 | [`PerronWright.CountableTVWindowProfile.windowDistance`](../PerronWright/Probability/CountableTVWindowProfile.lean#L27) |
| 标记距离达到阈值 `δ` 的坏标记集合 | [`PerronWright.CountableTVWindowProfile.badMarkCell`](../PerronWright/Probability/CountableTVWindowProfile.lean#L102) |
| 窗口标记距离总和的实际图期望 | [`PerronWright.CountableKernel.growingWindowDistanceExpectation`](../PerronWright/Probability/CountableTVWindowExpectation.lean#L94) |
| 窗口中至少存在一个坏标记原子的实际概率 | [`PerronWright.CountableKernel.growingWindowBadProbability`](../PerronWright/Probability/CountableTVWindowTerminal.lean#L22) |

这些距离期望和坏标记概率控制使用未加 starred 尺度的原始大小窗口；starred 法则本身通过正大小缩放转移到相应闭窗口。公共主定理同时给出这两种表述，不能把定量控制误写成新的外部收敛假设。
