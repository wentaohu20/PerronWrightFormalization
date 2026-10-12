# Perron–Wright 枚举主定理与定义索引

本页索引有限不可约模型与规则临界紧致模型的 Perron–Wright 枚举结果。所有链接指向定义或定理声明所在的源文件行；完整定理类型及证明以该处 Lean 源码为准。概率过程、Brownian 密度及可数模型的索引见本目录的其他文档。

## 主定理入口

| 分支 | 完整 Lean 名称及位置 | 结论范围 |
| --- | --- | --- |
| 有限不可约 | [PerronWright.FiniteIrreduciblePerronWrightTerminal.finite_perronWright](../PerronWright/Analysis/FiniteIrreduciblePerronWrightTerminal.lean#L120) | 真实树级数半径的解析性、在 `t=1` 的归一化、局部对数二次展开及三次余项；任意有限 surplus 截断下的统一缩窗半径公式与临界高斯公式。 |
| 规则临界紧致 | [PerronWright.CompactPerronWrightTheorem.compactPerronWright_theorem](../PerronWright/Enumeration/CompactPerronWrightTheorem.lean#L232) | 对每个 surplus 截断 `R` 给出解析半径、真实级数半径识别、局部对数展开及两种统一枚举公式。 |
| 紧致结论的展开定义 | [PerronWright.CompactPerronWrightTheorem.CompactPerronWrightConclusions](../PerronWright/Enumeration/CompactPerronWrightTheorem.lean#L193) | 查看总终端各个字段的确切类型与量词顺序。 |

有限分支只要求不可约，不要求核严格正或本原，因而没有排除二部核。紧致枚举分支要求 `B1`–`B2`；这里没有概率分支的 `QP` 假设。

## 1. 模型及临界假设

| 数学对象 | 完整 Lean 名称及定义位置 | 含义 |
| --- | --- | --- |
| 连续核 | [PerronWright.ContinuousKernel](../PerronWright/Kernel/Basic.lean#L27) | 连续、对称、处处非负的实核 `κ(x,y)`。 |
| 有限模型 | [PerronWright.FiniteIrreducibleModel](../PerronWright/Model/FiniteIrreducibleModel.lean#L22) | 有限类型集、严格正且和为一的类型权重，以及对称非负不可约核矩阵；非负性由不可约矩阵数据获得。 |
| 有限类型测度 | [PerronWright.FiniteIrreducibleModel.measure](../PerronWright/Model/FiniteIrreducibleModel.lean#L56) | `μ = Σ_a weight(a) δ_a`。 |
| 有限均值矩阵 | [PerronWright.FiniteIrreducibleModel.meanMatrix](../PerronWright/Model/FiniteIrreducibleModel.lean#L44) | `κ diag(weight)`，其 `(a,b)` 元素为 `κ(a,b) weight(b)`。 |
| 有限临界性 | [PerronWright.FiniteIrreducibleModel.IsCritical](../PerronWright/Model/FiniteIrreducibleModel.lean#L51) | 上述真实均值矩阵的谱半径等于一。 |
| 紧致模型 | [PerronWright.CompactBJRModel](../PerronWright/Model/CompactBJR.lean#L29) | 紧致度量类型空间、满支撑 Borel 概率测度 `μ` 与连续核 `κ`。 |
| B1 的算子见证 | [PerronWright.CompactBJRModel.B1Witness](../PerronWright/Model/CompactBJR.lean#L85) | 与给定核关联的 `L²(μ)` 算子紧致、自伴且范数等于一；不是任意无关算子的见证。 |
| B1 | [PerronWright.CompactBJRModel.B1](../PerronWright/Model/CompactBJR.lean#L93) | 存在上述算子见证。 |
| B2 | [PerronWright.CompactBJRModel.B2](../PerronWright/Model/CompactBJR.lean#L174) | 某一正次幂的真实迭代核处处严格正。 |
| 规则临界性 | [PerronWright.CompactBJRModel.IsRegularCritical](../PerronWright/Model/CompactBJR.lean#L191) | 同时满足 B1 与 B2。 |
| 有限模型的数据适配 | [PerronWright.FiniteIrreducibleModel.bjrModel](../PerronWright/Model/FiniteIrreducibleBJRBridge.lean#L62) | 把有限模型作为离散连续 BJR 数据，供统一图权重定义使用；它没有附加 B2 或规则临界性。 |

有限终端中的度量、离散拓扑与 Borel 类型类用于离散连续表示；真正的有限谱临界假设仍是 `IsCritical`。

## 2. 核算子及度函数

| 数学对象 | 完整 Lean 名称及定义位置 | 含义 |
| --- | --- | --- |
| `L²(μ)` 空间 | [PerronWright.CompactBJRModel.L2](../PerronWright/Model/CompactBJR.lean#L52) | 核的 Hilbert 空间实现。 |
| 点态积分作用 | [PerronWright.CompactBJRModel.integralAction](../PerronWright/Model/CompactBJR.lean#L60) | `Kf(x)=∫ κ(x,y)f(y) μ(dy)`。 |
| 核与 `L²` 算子的对应 | [PerronWright.CompactBJRModel.IsAssociatedL2Operator](../PerronWright/Model/CompactBJR.lean#L71) | 对连续测试函数的弱配对等于核积分配对。 |
| 连续函数上的有界算子 | [PerronWright.ContinuousKernel.actionCLM](../PerronWright/Kernel/Integral.lean#L165) | 同一积分作用在 `C(S,ℝ)` 上的连续线性映射。 |
| 有限作用 | [PerronWright.FiniteIrreducibleModel.action](../PerronWright/Model/FiniteIrreduciblePerronQuantities.lean#L20) | `Kf(a)=Σ_b κ(a,b) weight(b) f(b)`。 |
| 迭代核 | [PerronWright.CompactBJRModel.iteratedKernel](../PerronWright/Model/CompactBJR.lean#L102) | 下标 `n` 表示 `K^(n+1)` 的核，不表示 `K^n`；`n=0` 即原核。 |
| 迭代核的连续封装 | [PerronWright.CompactBJRModel.iteratedKernelMap](../PerronWright/Model/CompactBJR.lean#L118) | B2 使用的连续迭代积分核。 |
| 度函数 | [PerronWright.ContinuousKernel.degree](../PerronWright/Kernel/Basic.lean#L85) | `d(x)=∫ κ(x,y) μ(dy)`。 |
| 连续度函数 | [PerronWright.CompactBJRModel.degreeFunction](../PerronWright/Model/PerronQuantities.lean#L128) | 度函数的 `C(S,ℝ)` 封装。 |

## 3. Perron 归一化及尺度

记 `u` 为严格正的 Perron 函数。这里使用的是 **类型平均等于一** 的归一化，不是 `L²` 范数等于一：

\[
Ku=u,\qquad \int u\,d\mu=1,\qquad
\alpha=\int u^2\,d\mu,\qquad \beta=\int u^3\,d\mu.
\]

有限模型把积分换成以 `weight` 加权的有限和。`α`、`β` 是从模型假设证明得到的 Perron 函数所定义的尺度，不是附加模型参数。

| 数学对象 | 完整 Lean 名称及位置 |
| --- | --- |
| 有限类型平均 | [PerronWright.FiniteIrreducibleModel.average](../PerronWright/Model/FiniteIrreduciblePerronQuantities.lean#L90) |
| 有限 Perron 函数 | [PerronWright.FiniteIrreducibleModel.perronFunction](../PerronWright/Model/FiniteIrreduciblePerronQuantities.lean#L124) |
| 有限固定点及归一化证明 | [PerronWright.FiniteIrreducibleModel.perronFunction_fixed](../PerronWright/Model/FiniteIrreduciblePerronQuantities.lean#L131)；[PerronWright.FiniteIrreducibleModel.perronFunction_average](../PerronWright/Model/FiniteIrreduciblePerronQuantities.lean#L135) |
| 有限 `α`、`β` | [PerronWright.FiniteIrreducibleModel.alpha](../PerronWright/Model/FiniteIrreduciblePerronQuantities.lean#L139)；[PerronWright.FiniteIrreducibleModel.beta](../PerronWright/Model/FiniteIrreduciblePerronQuantities.lean#L142) |
| 紧致 Perron 函数 | [PerronWright.CompactBJRModel.perronFunction](../PerronWright/Model/PerronQuantities.lean#L22) |
| 紧致固定点及归一化证明 | [PerronWright.CompactBJRModel.perronFunction_fixed](../PerronWright/Model/PerronQuantities.lean#L29)；[PerronWright.CompactBJRModel.perronFunction_integral](../PerronWright/Model/PerronQuantities.lean#L33) |
| 紧致 `α`、`β` | [PerronWright.CompactBJRModel.alpha](../PerronWright/Model/PerronQuantities.lean#L92)；[PerronWright.CompactBJRModel.beta](../PerronWright/Model/PerronQuantities.lean#L96) |
| Perron 概率 `u(x)μ(dx)` | [PerronWright.CompactBJRModel.perronLaw](../PerronWright/Model/PerronQuantities.lean#L57) |

## 4. 加权图计数与标量外场

`k` 是顶点数，`r` 是 surplus：连通图有 `k+r−1` 条边。`r=0` 是树，`r=1` 是单环；正 excess 分支使用 `ell=r−1`，因此该分支 `ell>0` 对应 `r≥2`。

对标号简单图 `H`，真实 annealed 权重为

\[
W_t(H)=\int_{S^k}
\left(\prod_{i=1}^k e^{-t d(x_i)}\right)
\left(\prod_{\{i,j\}\in E(H)}t\kappa(x_i,x_j)\right)
\,d\mu^{\otimes k}(x),
\qquad
C_t(k,r)=\sum_{\substack{H\text{ 连通}\cr |E(H)|=k+r-1}}W_t(H).
\]

这是直接对有限简单图求和并积分的定义，不是以某个渐近主项代替图权重。有限模型使用 `M.bjrModel.connectedWeight`，与紧致分支共享同一个定义。

| 数学对象 | 完整 Lean 名称及定义位置 |
| --- | --- |
| 无序边因子 | [PerronWright.CompactBJRModel.edgeFactor](../PerronWright/Enumeration/ConnectedWeight.lean#L27) |
| 图的权重 integrand | [PerronWright.CompactBJRModel.graphWeightIntegrand](../PerronWright/Enumeration/ConnectedWeight.lean#L39) |
| 对类型向量作产品测度积分 | [PerronWright.CompactBJRModel.graphWeight](../PerronWright/Enumeration/ConnectedWeight.lean#L46) |
| 连通固定顶点数、固定 surplus 权重 | [PerronWright.CompactBJRModel.connectedWeight](../PerronWright/Enumeration/ConnectedWeight.lean#L53) |
| 实标量外场 `g_t(x)=log t−(t−1)d(x)` | [PerronWright.CompactBJRModel.scalarField](../PerronWright/Enumeration/FieldWeight.lean#L81) |
| 外场图 integrand | [PerronWright.CompactBJRModel.fieldGraphWeightIntegrand](../PerronWright/Enumeration/FieldWeight.lean#L87) |
| 外场图积分及连通总和 | [PerronWright.CompactBJRModel.fieldGraphWeight](../PerronWright/Enumeration/FieldWeight.lean#L92)；[PerronWright.CompactBJRModel.fieldConnectedWeight](../PerronWright/Enumeration/FieldWeight.lean#L97) |
| 复外场图 integrand | [PerronWright.CompactBJRModel.complexFieldGraphIntegrand](../PerronWright/Enumeration/FieldAnalytic.lean#L82) |
| 紧致复标量外场 | [PerronWright.ScalarFieldResponse.scalarFieldComplex](../PerronWright/Analysis/ScalarFieldResponse.lean#L14) |
| 有限复标量外场适配 | [PerronWright.FiniteIrreducibleScalarFieldResponse.scalarField](../PerronWright/Analysis/FiniteIrreducibleScalarFieldResponse.lean#L22) |

实外场版本把顶点因子改成 `exp(g(x_i)−d(x_i))`，边因子改成 `κ(x_i,x_j)`。对 `t>0`，源码的 [标量外场恒等式](../PerronWright/Enumeration/FieldWeight.lean#L194) 为 `C_t(k,r)=t^(r−1) C_{g_t}(k,r)`，包括树分支的 `t⁻¹` 因子。

## 5. 树级数、解析临界对与真实半径

树级数来自真实有限标号树积分：固定根类型，积分其余顶点类型，再对树求和；次数 `n+1` 的系数除以 `n!`。

| 数学对象 | 完整 Lean 名称及定义位置 |
| --- | --- |
| 固定根类型的图积分 | [PerronWright.FieldRootedTree.fixedRootedGraphProfileMap](../PerronWright/Enumeration/FieldRootedTreeFinite.lean#L192) |
| 真标号树总和 | [PerronWright.FieldRootedTree.numerator](../PerronWright/Enumeration/FieldRootedTreeFinite.lean#L216) |
| 阶乘归一化系数 | [PerronWright.FieldRootedTree.coefficient](../PerronWright/Enumeration/FieldRootedTreeFinite.lean#L222) |
| 真外场树形式幂级数 | [PerronWright.FieldRootedTree.series](../PerronWright/Enumeration/FieldRootedTreeFinite.lean#L256) |
| 紧致树级数的 multilinear 封装 | [PerronWright.FieldRootedTree.fms](../PerronWright/Enumeration/ScalarFieldRootedTreeRadius.lean#L41) |
| 有限模型同一真图级数的封装 | [PerronWright.FiniteIrreducibleModel.fieldFMS](../PerronWright/Analysis/FiniteIrreducibleFieldSeriesNormalization.lean#L58) |
| 紧致解析临界对 `(ρ_g,τ_g)` | [PerronWright.CriticalPair.criticalPair](../PerronWright/Analysis/CriticalPair.lean#L341) |
| 有限解析临界对 | [PerronWright.FiniteIrreducibleCriticalPair.criticalPair](../PerronWright/Analysis/FiniteIrreducibleCriticalPair.lean#L342) |
| 紧致临界对的半径分量 | [PerronWright.RadiusResponse.radius](../PerronWright/Analysis/RadiusResponse.lean#L23) |
| 有限临界对的半径分量 | [PerronWright.FiniteIrreducibleRadiusResponse.radius](../PerronWright/Analysis/FiniteIrreducibleRadiusResponse.lean#L23) |
| 紧致标量切片 `ρ(g_t)` | [PerronWright.ScalarRadiusSecond.scalarRadius](../PerronWright/Analysis/ScalarRadiusSecond.lean#L13) |
| 有限标量切片 | [PerronWright.FiniteIrreducibleScalarFieldResponse.scalarRadius](../PerronWright/Analysis/FiniteIrreducibleScalarFieldResponse.lean#L25) |
| 紧致物理实半径 `ρ(t)` | [PerronWright.CriticalWindowRadiusConversion.realScalarRadius](../PerronWright/Analysis/CriticalWindowRadiusConversion.lean#L23) |
| 有限物理实半径 `ρ(t)` | [PerronWright.FiniteIrreducibleCriticalWindowRadiusConversion.realScalarRadius](../PerronWright/Analysis/FiniteIrreducibleCriticalWindowRadiusConversion.lean#L23) |
| 紧致解析对数 | [PerronWright.ScalarLogRadiusTaylor.logScalarRadius](../PerronWright/Analysis/ScalarLogRadiusTaylor.lean#L57) |
| 有限解析对数 | [PerronWright.FiniteIrreducibleScalarLogRadiusTaylor.logScalarRadius](../PerronWright/Analysis/FiniteIrreducibleScalarLogRadiusTaylor.lean#L66) |
| 紧致二次率 `α²/(2β)` | [PerronWright.CriticalWindowRadiusConversion.criticalQuadraticRate](../PerronWright/Analysis/CriticalWindowRadiusConversion.lean#L28) |
| 有限二次率 | [PerronWright.FiniteIrreducibleCriticalWindowRadiusConversion.criticalQuadraticRate](../PerronWright/Analysis/FiniteIrreducibleCriticalWindowRadiusConversion.lean#L28) |
| 紧致主定理公开的复半径、实半径与对数别名 | [PerronWright.CompactPerronWrightTheorem.ScalarRadius.criticalRadius](../PerronWright/Enumeration/CompactPerronWrightTheorem.lean#L28)；[PerronWright.CompactPerronWrightTheorem.ScalarRadius.physicalRadius](../PerronWright/Enumeration/CompactPerronWrightTheorem.lean#L34)；[PerronWright.CompactPerronWrightTheorem.ScalarRadius.logCriticalRadius](../PerronWright/Enumeration/CompactPerronWrightTheorem.lean#L40) |
| 紧致/有限主项使用的物理树半径别名 | [PerronWright.TreePerronWrightFormula.physicalTreeRadius](../PerronWright/Enumeration/TreePerronWrightFormula.lean#L50)；[PerronWright.FiniteIrreducibleTreePerronWrightFormula.physicalTreeRadius](../PerronWright/Analysis/FiniteIrreducibleTreePerronWrightFormula.lean#L50) |

临界对由解析构造得到，同时满足树方程与特征值一约束；具体方程见 [紧致 `criticalPair_germ`](../PerronWright/Analysis/CriticalPair.lean#L242) 和 [有限 `criticalPair_germ`](../PerronWright/Analysis/FiniteIrreducibleCriticalPair.lean#L246)。它不是额外假定的枚举或半径接口。

半径的记号须分清：

- `ρ_g` 是复外场下的解析临界活动；实标量切片 `ρ(t)=ρ_{g_t}` 在 `t=1` 附近为正，且 `ρ(1)=1`。
- 源码中的 `physicalRadius`、`realScalarRadius`、`physicalTreeRadius` 是这个 `ρ(t)` 的物理实分支；它本身等于真外场树级数的收敛半径。识别定理见 [有限半径识别](../PerronWright/Analysis/FiniteIrreduciblePhysicalScalarRadius.lean#L46) 与 [紧致半径识别](../PerronWright/Enumeration/CompactPerronWrightTheorem.lean#L135)。
- 主项的 `ρ(t)^(−k)e^(−k)` 可以合并写成 `(eρ(t))^(−k)`。这里 `eρ(t)` 仅是组合主项的指数尺度，**不是**上述树级数收敛半径，也不是源码中另一项独立半径定义；`e^(−k)` 来自阶乘/Stirling 转换。

总终端的局部半径展开为

\[
\log\rho(t)=\frac{\alpha^2}{2\beta}(t-1)^2+O(|t-1|^3).
\]

## 6. Wright 常数与半径/高斯主项

统一 Wright 常数以 surplus `r` 索引：`w_0=1`，`w_1=√(2π)/4=√(π/8)`；`r≥2` 时使用正 excess `ell=r−1` 的有限连通立方核和。核允许环与平行边，但最终 `connectedWeight` 始终是简单图权重。

| 数学对象 | 完整 Lean 名称及定义位置 | 含义 |
| --- | --- | --- |
| 有限多重图 | [PerronWright.FiniteMultiGraph](../PerronWright/Enumeration/KernelBounds.lean#L14) | 带边标签及无序端点的有限多重图。 |
| 连通立方核 | [PerronWright.GraphCore.LabelledConnectedCubicKernel](../PerronWright/Enumeration/CubicKernelSubdivision.lean#L33) | `2ell` 个顶点、`3ell` 条边，每个顶点度为三；非环简单支撑连通。 |
| 核的全局表示重数 | [PerronWright.GraphCore.labelledCubicKernelGlobalMultiplicity](../PerronWright/Enumeration/PositiveSurplusWrightConstant.lean#L221) | `(2ell)! (3ell)!` 乘环方向因子。 |
| 重数倒数 | [PerronWright.GraphCore.labelledCubicKernelInverseMultiplicityReal](../PerronWright/Enumeration/PositiveSurplusCubicConstantPositivity.lean#L29) | 立方核有限和中每个核的权重。 |
| 立方核 EGF 常数 | [PerronWright.GraphCore.positiveSurplusCubicEGFConstantReal](../PerronWright/Enumeration/PositiveSurplusCubicConstantPositivity.lean#L46) | 重数倒数的有限和乘 `2^(−3ell/2)`。 |
| 正 excess Wright 常数 | [PerronWright.GraphCore.positiveSurplusWrightConstantReal](../PerronWright/Enumeration/PositiveSurplusCubicConstantPositivity.lean#L110) | EGF 常数乘 `√(2π)/Γ(3ell/2)`。 |
| 单环常数 | [PerronWright.UnicyclicPerronWrightFormula.unicyclicWrightConstant](../PerronWright/Enumeration/UnicyclicPerronWrightFormula.lean#L57) | `√(2π)/4`。 |
| 紧致统一 `w_r` | [PerronWright.PerronWrightFormulaMainTerm.wrightConstant](../PerronWright/Enumeration/PerronWrightFormulaMainTerm.lean#L25) | 合并树、单环与正 excess 三个分支。 |
| 有限统一 `w_r` | [PerronWright.FiniteIrreduciblePerronWrightFormulaMainTerm.wrightConstant](../PerronWright/Analysis/FiniteIrreduciblePerronWrightFormulaMainTerm.lean#L26) | 与紧致分支是相同常数族，非模型依赖常数。 |
| 紧致半径主项 | [PerronWright.PerronWrightFormulaMainTerm.perronWrightRadiusMainTerm](../PerronWright/Enumeration/PerronWrightFormulaMainTerm.lean#L58) | 下式 `A_ρ`。 |
| 有限半径主项 | [PerronWright.FiniteIrreduciblePerronWrightFormulaMainTerm.perronWrightRadiusMainTerm](../PerronWright/Analysis/FiniteIrreduciblePerronWrightFormulaMainTerm.lean#L64) | 同一形式，使用有限 `β` 与半径。 |
| 紧致高斯主项 | [PerronWright.BoundedSurplusPerronWrightFormula.perronWrightGaussianMainTerm](../PerronWright/Enumeration/BoundedSurplusPerronWrightFormula.lean#L131) | 下式 `A_G`。 |
| 有限高斯主项 | [PerronWright.FiniteIrreducibleBoundedSurplusPerronWrightFormula.perronWrightGaussianMainTerm](../PerronWright/Analysis/FiniteIrreducibleBoundedSurplusPerronWrightFormula.lean#L131) | 同一形式，使用有限 `α`、`β`。 |

对正整数 `k`，两个主项为

\[
A_\rho(k,r,t)=w_r\beta^{(r-1)/2}\rho(t)^{-k}e^{-k}k^{k+3r/2-2},
\]

\[
A_G(k,r,t)=w_r\beta^{(r-1)/2}e^{-k}k^{k+3r/2-2}
\exp\!\left(-\frac{\alpha^2}{2\beta}k(t-1)^2\right).
\]

主定理把真实 `C_t(k,r)` 与这些主项比较。对任意固定 `R` 与非负缩窗 `η(k)→0`，半径公式的相对误差为 `O(η(k)+k^(−1/2))`，同时覆盖 `r≤R` 和 `|t−1|≤η(k)`；常数先于 `η` 选定。对固定 `L≥0` 的临界窗 `|t−1|≤L/√k`，高斯公式的相对误差为 `O(k^(−1/2))`，同时覆盖所有 `r≤R` 与窗内的 `t`。

`AnalyticAt` 表示局部解析，`Tendsto` 表示极限，`=O` 表示大 O 估计，`∀ᶠ k in atTop` 表示所有充分大的自然数 `k`；这些是 Mathlib 的通用记号。它们的具体量词以本页首列出的两个总终端及紧致结论结构为准。本索引不记录机器运行或构建测试状态。
