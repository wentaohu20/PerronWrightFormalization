# Perron–Wright 形式化证明

Lean 4 形式化项目，覆盖论文第三章的枚举、局部阶乘密度、实际 Brownian 点过程极限以及可数类型增长支撑结论。证明源码统一由 [PerronWright.lean](PerronWright.lean) 导入。

本仓库固定 **Lean / mathlib v4.33.1**，具体版本与依赖提交分别见 [lean-toolchain](lean-toolchain)、[lakefile.toml](lakefile.toml) 和 [lake-manifest.json](lake-manifest.json)。主定理的假设以链接中的 Lean 声明为准；不同模型的条件不能互换。

最近一次实际验证及其范围见 [验证记录](docs/VERIFICATION.md)。

## 一键构建与验证

先安装 [Lean 的 Elan 工具链管理器](https://lean-lang.org/install/)，确保 `lake` 在终端路径中。无需另外安装 Python、Node.js 或 GitHub CLI。

Windows：双击仓库根目录的 **[verify.cmd](verify.cmd)**，或者在 PowerShell 中运行：

```powershell
.\Verify.ps1
```

Linux / macOS：

```sh
bash verify.sh
```

入口依次获取固定版本的 mathlib 缓存、构建全部证明模块、读取已检查的主定理证明表达式，并**逐个打印定理依赖和公理依赖**。首次运行需要网络、下载空间和较长的构建时间；之后可以复用本地缓存。报错会返回非零退出码。

Windows 可额外运行全部三个历史公理审计入口：

```powershell
.\Verify.ps1 -FullAudit
```

已有依赖和缓存时，可使用 `-SkipCache`；Unix 对应 `SKIP_CACHE=1 bash verify.sh`，扩展审计对应 `FULL_AUDIT=1 bash verify.sh`。

验证产物位于本地 `.verification/`，不上传到仓库：

| 文件 | 内容 |
| --- | --- |
| `build.log` | 完整构建输出 |
| `main-theorem-dependencies.log` | 每个主定理逐条打印的直接证明定理、传递项目定理数量与公理 |
| `main-theorem-dependencies.json` | 定理陈述、完整传递常量闭包、每个声明的直接依赖及源码位置，可重建依赖图 |
| `main-theorem-definitions.md` | 从主定理类型和证明实际可达的全部项目定义索引，包括生成的辅助声明 |

依赖打印器是 [MainTheoremDependencies.lean](MainTheoremDependencies.lean)。它穿过定义继续追踪证明，不用模块导入列表或单独的 `#print axioms` 冒充定理依赖。它检查下面 **21 个公共声明**；这不是说论文有 21 个独立主定理，而是按模型与结论拆分后的 Lean 入口。公理单独报告，只允许 Lean 的标准 `propext`、`Classical.choice`、`Quot.sound`；出现 `sorryAx` 等非标准公理即失败。该检查程序不被数学证明导入，也不增加数学假设。

## 主定理在哪里

下列声明名省略公共前缀 `PerronWright.`。点击源码行号即可查看完整陈述、量词顺序、假设和证明。

### 1. Perron–Wright 枚举公式

| 模型 | 公共声明 | 位置 |
| --- | --- | --- |
| 有限不可约临界类型 | `FiniteIrreduciblePerronWrightTerminal.finite_perronWright` | [FiniteIrreduciblePerronWrightTerminal.lean:120](PerronWright/Analysis/FiniteIrreduciblePerronWrightTerminal.lean#L120) |
| 正则紧致临界 BJR 类型 | `CompactPerronWrightTheorem.compactPerronWright_theorem` | [CompactPerronWrightTheorem.lean:232](PerronWright/Enumeration/CompactPerronWrightTheorem.lean#L232) |

紧致版本返回的全部结论字段在 [CompactPerronWrightConclusions:193](PerronWright/Enumeration/CompactPerronWrightTheorem.lean#L193)。两个版本均包含真正树级数临界半径的解析性、`ρ(1)=1`、三阶误差控制，以及有界 surplus 范围的一致公式：

$$
C_t(k,r)=w_r\beta^{(r-1)/2}e^{-k}\rho(t)^{-k}
k^{k+3r/2-2}\{1+O_R(\eta_k+k^{-1/2})\},\qquad |t-1|\le\eta_k\to0.
$$

在 `|t−1|≤Lk⁻¹ᐟ²` 上，还给出替换 `ρ(t)⁻ᵏ` 后的高斯形式。**`ρ` 是源码所定义树级数的收敛半径；`eρ` 只是上述主项的指数尺度，不是另一个树级数半径。** 此处紧致枚举定理不要求下面概率部分的 `QP` 条件。

### 2. 实际 Brownian 阶乘密度与确定性

| 结论 | 公共声明 | 位置 |
| --- | --- | --- |
| 有序 excursion 源的密度 | `BrownianActualFactorialDensity.actual_ordered_source_factorial_density` | [源码:64](PerronWright/Probability/BrownianActualFactorialDensity.lean#L64) |
| 窗口点测度的阶乘密度 | `BrownianActualFactorialDensity.actual_window_factorial_density` | [源码:136](PerronWright/Probability/BrownianActualFactorialDensity.lean#L136) |
| 全部混合阶乘矩确定 cell-count 法则 | `BrownianActualArbitraryWindowDeterminacy.actual_cell_countLaw_eq_of_factorial_lintegrals` | [源码:36](PerronWright/Probability/BrownianActualArbitraryWindowDeterminacy.lean#L36) |
| 阶乘密度确定窗口点过程法则 | `BrownianActualArbitraryWindowDeterminacy.actual_windowLaw_eq_of_density_factorial_lintegrals` | [源码:95](PerronWright/Probability/BrownianActualArbitraryWindowDeterminacy.lean#L95) |

这些入口使用实际连续 Brownian 路径、反射 excursion 和给定路径后以 excursion 面积为率的 Poisson 标记，不是把 Brownian 识别作为外部接口假定。

### 3. 实际有限图的局部阶乘期望公式

| 模型 | 公共声明 | 位置 |
| --- | --- | --- |
| 固定类型赋值，人数误差 `O(1)` | `FiniteIrreducibleLocalMainTerminal.eventually_uniform_paper_floor_factorial_density` | [源码:34](PerronWright/Probability/FiniteIrreducibleLocalMainTerminal.lean#L34) |
| 正则紧致模型，加 `QP` | `CompactAnnealedFactorialUniform.factorial_uniform_bounded_surplus` | [源码:44](PerronWright/Probability/CompactAnnealedFactorialUniform.lean#L44) |

结论对固定正大小窗口、所有有界 surplus 元组一致，组件大小使用真正的整数取整 `⌊x n^(2/3)⌋`，计数对象是有序、互不相同的真实连通组件。

### 4. 实际点过程及经验类型标记的 Brownian 极限

全部声明在命名空间 `PerronWright.ModelActualBrownianLimits`：

| 结论 | 有限不可约模型的声明与位置 | 正则紧致模型的声明与位置 |
| --- | --- | --- |
| 无标记闭窗口 | [`finite_windowLaw_tendsto_actual_Brownian`:45](PerronWright/Probability/ModelActualBrownianLimits.lean#L45) | [`compact_windowLaw_tendsto_actual_Brownian`:158](PerronWright/Probability/ModelActualBrownianLimits.lean#L158) |
| 无标记全局 vague 法则 | [`finite_processLaw_tendsto_actual_Brownian`:63](PerronWright/Probability/ModelActualBrownianLimits.lean#L63) | [`compact_processLaw_tendsto_actual_Brownian`:173](PerronWright/Probability/ModelActualBrownianLimits.lean#L173) |
| 经验标记闭窗口 | [`finite_markedWindowLaw_tendsto_actual_Brownian`:80](PerronWright/Probability/ModelActualBrownianLimits.lean#L80) | [`compact_markedWindowLaw_tendsto_actual_Brownian`:187](PerronWright/Probability/ModelActualBrownianLimits.lean#L187) |
| 经验标记全局法则 | [`finite_markedProcessLaw_tendsto_actual_Brownian`:97](PerronWright/Probability/ModelActualBrownianLimits.lean#L97) | [`compact_markedProcessLaw_tendsto_actual_Brownian`:201](PerronWright/Probability/ModelActualBrownianLimits.lean#L201) |
| starred 无标记全局法则 | [`finite_starredProcessLaw_tendsto_actual_Brownian`:113](PerronWright/Probability/ModelActualBrownianLimits.lean#L113) | [`compact_starredProcessLaw_tendsto_actual_Brownian`:215](PerronWright/Probability/ModelActualBrownianLimits.lean#L215) |
| starred 经验标记全局法则 | [`finite_starredMarkedProcessLaw_tendsto_actual_Brownian`:128](PerronWright/Probability/ModelActualBrownianLimits.lean#L128) | [`compact_starredMarkedProcessLaw_tendsto_actual_Brownian`:229](PerronWright/Probability/ModelActualBrownianLimits.lean#L229) |

有限模型允许任意满足有界人数误差的实际固定类型赋值；紧致概率结论要求 `IsRegularCritical` 和 `QP`。starred 只把大小乘以 `β^(1/3)`，不改变 surplus 或经验类型标记；Brownian 参数为 `Λ=αβ^(−2/3)λ`。未 starred 的极限是相应 Brownian 大小逆缩放法则。极限类型标记是 `u·μ`，不是原始 `μ`。

### 5. 可数类型：同一增长支撑与精确整数图源

公共声明：

`PerronWright.CountableActualBrownianLimits.exists_actual_growing_Brownian_global_and_TV_window_limits`

位置：[CountableActualBrownianLimits.lean:90](PerronWright/Probability/CountableActualBrownianLimits.lean#L90)。同一个最外层 `∃ level` 给出支撑穷尽、精确整数人数、局部公式、starred 无标记全局极限、无标记和 TV 标记窗口极限，以及标记偏差的定量控制。

谱归一化图源使用 hazard `tκ/(Nσ_n)`；原始图源使用 `tκ/N`。原始分支在 `N^(1/3)(σ_n−1)→θ` 时，局部参数为 **`λ+θ`**，Brownian 参数为 **`αβ^(−2/3)(λ+θ)`**。不能省略漂移假设。这里的 TV 是**组件类型标记空间的距离**，窗口法则仍是弱分布收敛；不是整个过程概率法则之间的总变差收敛。可数终端的全局结论仅为无标记 vague-law 收敛。

## 相关定义在哪里

下表是读主定理所需的核心定义导航；各分支的全部语义定义、完整声明名和源码行号见紧随其后的详细索引。机器生成的传递定义索引进一步覆盖证明中使用的所有内部辅助对象。

| 概念 | 主要定义与位置 |
| --- | --- |
| 有限不可约类型模型、临界性 | [`FiniteIrreducibleModel`:22](PerronWright/Model/FiniteIrreducibleModel.lean#L22)、[`IsCritical`:51](PerronWright/Model/FiniteIrreducibleModel.lean#L51) |
| 紧致 BJR 模型、B1/B2、正则临界性 | [`CompactBJRModel`:29](PerronWright/Model/CompactBJR.lean#L29)、[B1:93](PerronWright/Model/CompactBJR.lean#L93)、[B2:174](PerronWright/Model/CompactBJR.lean#L174)、[正则临界性:191](PerronWright/Model/CompactBJR.lean#L191) |
| 可数模型与正则临界性 | [`CountableKernel`:19](PerronWright/Model/CountableKernel.lean#L19)、[`IsRegularCritical`:18](PerronWright/Model/CountablePerronQuantities.lean#L18) |
| 紧致概率分支的 `QP` 条件 | [`CompactBJRModel.QP`:82](PerronWright/Probability/ProjectiveKernel.lean#L82)：核有绝对可求和的二次 feature 展开；不是类型人数条件 |
| 规范化 Perron 函数、Perron 法则、`α`、`β` | [紧致 PerronQuantities](PerronWright/Model/PerronQuantities.lean#L22)、[有限 PerronQuantities](PerronWright/Model/FiniteIrreduciblePerronQuantities.lean#L124)、[可数 PerronQuantities](PerronWright/Model/CountablePerronQuantities.lean#L27) |
| `C_t(k,r)`：核加权连通图枚举 | [`connectedWeight`:53](PerronWright/Enumeration/ConnectedWeight.lean#L53)、[`fieldConnectedWeight`:97](PerronWright/Enumeration/FieldWeight.lean#L97) |
| 根树级数与真正临界半径 | [`FieldRootedTree.fms`:41](PerronWright/Enumeration/ScalarFieldRootedTreeRadius.lean#L41)、[`ScalarRadius.physicalRadius`:34](PerronWright/Enumeration/CompactPerronWrightTheorem.lean#L34) |
| Wright 常数与完整主项 | [`wrightConstant`:25](PerronWright/Enumeration/PerronWrightFormulaMainTerm.lean#L25)、[`perronWrightRadiusMainTerm`:58](PerronWright/Enumeration/PerronWrightFormulaMainTerm.lean#L58) |
| 实际有限 / 紧致图概率测度 | [`FiniteIrreducibleTypedGraphLaw.law`:52](PerronWright/Probability/FiniteIrreducibleTypedGraphLaw.lean#L52)、[`AnnealedGraph.law`:166](PerronWright/Probability/AnnealedGraph.lean#L166) |
| 临界时间、组件整数大小、有序组件计数 | [CriticalScaling:24、49](PerronWright/Probability/CriticalScaling.lean#L24)、[`ComponentCounts.count`:60](PerronWright/Probability/ComponentCounts.lean#L60) |
| 局部目标阶乘密度 | [`FactorialDensity.density`:29](PerronWright/Probability/FactorialDensity.lean#L29)，指数和大小因子在同文件 :19、:24 |
| 有限窗口点测度、全局局部有限点测度 | [`PointMeasure`:33](PerronWright/Probability/FinitePointMeasureCompact.lean#L33)、[`SurplusWindow`:250](PerronWright/Probability/FinitePointMeasureCompact.lean#L250)、[`LocalPointMeasure`:29](PerronWright/Probability/LocallyFinitePointMeasureVague.lean#L29) |
| 实际 Brownian 路径及 excursion 点过程法则 | [`BrownianPathLaw.pathLaw`:111](PerronWright/Probability/BrownianPathLaw.lean#L111)、[`BrownianExcursionPointProcessLaw.law`:45](PerronWright/Probability/BrownianExcursionPointProcessLaw.lean#L45) |
| excursion 面积与条件 Poisson 标记 | [`excursionArea`:51](PerronWright/Probability/BrownianFullHorizonExcursionAreas.lean#L51)、[`markLaw`:78](PerronWright/Probability/BrownianFullHorizonPoissonMarks.lean#L78) |
| 组件经验类型标记与 Perron 标记 | [`componentMark`:75](PerronWright/Probability/EmpiricalTypeMarks.lean#L75)、[`perronMark`:118](PerronWright/Probability/EmpiricalTypeMarks.lean#L118) |
| 可数整数人数、谱半径与两种实际图源 | [GrowingTypeCounts](PerronWright/Probability/GrowingTypeCounts.lean#L57)、[`empiricalSpectralRadius`:55](PerronWright/Kernel/CountableApproximationEmpirical.lean#L55)、[CountableEmpiricalGraphLaw](PerronWright/Probability/CountableEmpiricalGraphLaw.lean#L25) |
| 可数 TV 类型标记 | [`VariationMark`:52](PerronWright/Probability/CountableVariationMarks.lean#L52)、[距离等式:72](PerronWright/Probability/CountableVariationMarks.lean#L72) |

详细索引：

- [枚举端：模型、算子、Perron 量、场、树半径、Wright 常数](docs/ENUMERATION_INDEX.md)
- [概率端：图源、密度、Brownian、拓扑、标记及归一化](docs/PROBABILITY_INDEX.md)
- [可数端：整数实现、谱漂移、点过程和 TV 标记](docs/COUNTABLE_INDEX.md)
- [主定理可达的全部项目定义（机器生成）](docs/MAIN_THEOREM_DEFINITIONS.md)

## 仓库结构与维护

```text
PerronWright/Kernel/        积分核、紧致性、谱与连续核实现
PerronWright/Model/         有限、紧致、可数模型及 Perron 量
PerronWright/Analysis/      解析扰动、隐函数、fold、谱分裂与转移
PerronWright/Enumeration/   图分解、核加权枚举、Wright 常数与系数公式
PerronWright/Probability/   实际图法则、阶乘矩、Brownian 与过程极限
docs/                      源码索引与保留的开发记录
Verify.ps1 / verify.cmd     Windows 一键构建及定理依赖检查
verify.sh                  Unix 同一验证入口
MainTheoremDependencies.lean  读取已检查证明的依赖打印器
```

数学证明源码与验证元程序分开；整理仓库不改变定理陈述或证明。编译缓存、临时试验、凭证文件与本地验证日志均不纳入 Git。原来的长 README 保存在 [开发历史](docs/DEVELOPMENT_HISTORY.md)；其中阶段性状态和旧接口不替代当前源码或以上索引。

若主定理名字改变，同时更新 `MainTheoremDependencies.lean`、本 README 和相应定义索引，再重新运行验证；不要用旧报告代替新构建。
