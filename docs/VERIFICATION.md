# 可复现验证记录

验证日期：2026-10-12（Asia/Shanghai）。这是一次实际运行记录；重新验证请使用仓库根目录的一键入口，而不是仅阅读本页。

## 实际运行

```powershell
.\Verify.ps1 -SkipCache -FullAudit
.\verify.cmd -SkipCache
```

两次均返回退出码 `0`。本机已有固定依赖和缓存，因此测试时使用 `-SkipCache`；首次克隆应使用默认入口获取缓存。另已检查 PowerShell 和 Bash 入口语法，未声称在 Linux/macOS 上完成同样的运行测试。

## 结果

| 项目 | 本次结果 |
| --- | --- |
| 数学证明源码 | 1,663 个 `PerronWright/` 下的 Lean 文件全部纳入仓库 |
| 完整构建 | `Build completed successfully (5356 jobs).` |
| 公共主定理入口 | 21 个，逐个读到实际证明表达式并打印直接证明定理依赖 |
| 类型与证明的传递常量闭包 | 88,559 个声明；没有未知、无法检查的节点 |
| 公理 | 仅 `propext`、`Classical.choice`、`Quot.sound`；未发现非标准公理 |
| 扩展审计 | `Audit.lean`、`ProbabilityAudit.lean`、`Chapter3FiniteProcessSpatialBridgeAudit.lean` 全部成功 |
| 构建及审计诊断 | 未发现 Lean 错误或警告 |
| 自动生成的定义位置 | 使用 Lean 从 1 开始的标识符位置；抽检密度、有限模型和紧致终端的行号与源码一致 |

完整本地输出在 `.verification/` 中。170 MB 左右的完整 JSON 依赖图和编译缓存不纳入 Git；较小的项目定义索引保存在 [MAIN_THEOREM_DEFINITIONS.md](MAIN_THEOREM_DEFINITIONS.md)。验证器会重新生成报告，不接受上次失败运行留下的旧 JSON。

该记录不是对数学定理假设的替代。特别是紧致概率分支的 `QP`、有限模型的人数误差和可数原始图源的谱漂移条件，请阅读 [README](../README.md) 及其链接中的完整 Lean 陈述。
