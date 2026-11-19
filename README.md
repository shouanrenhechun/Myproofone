# 最大度六的二部支配 · Bipartite domination at maximum degree six

本仓库的 Lean 4 工程以最大度至多六的非空、无孤立顶点的有限简单图为对象。源码包含二部支配比例的上界、一个达到上界的叶冠图，以及极值常数 c₆ = 8/15 的定理陈述和证明代码。

This Lean 4 project contains declarations for the bipartite domination bound for nonempty isolate-free graphs of maximum degree at most six, the sharp corona example, and the extremal ratio 8/15.

| 内容 | 源码 |
| --- | --- |
| 最大度六的上界 | [`main_upper_bound_minimum`](C6BipartiteDomination/MainResults.lean) |
| 叶冠锐例与精确极值 | [`corona_gamma_eq_eight` 和 `c6_eq_eight_fifteenths`](C6BipartiteDomination/ExtremalResults.lean) |
| 一般结构支配的转移接口与代数引理 | [`notes/DominationTransfer.lean`](notes/DominationTransfer.lean)，部分形式化，单独存放 |

## 构建

Lean 版本由 [lean-toolchain](lean-toolchain) 固定，mathlib 的版本和依赖提交由 [lakefile.toml](lakefile.toml) 及 [lake-manifest.json](lake-manifest.json) 固定。安装 elan 后，从仓库根目录运行：

```sh
lake exe cache get
lake build
```

本次整理没有重新编译工程。一般转移笔记未加入默认构建，且仍需核验编译。其覆盖范围是补全与预算接口及候选公式的若干恒等式。全参数极值、加权选择与叶冠图构造尚待形式化。

论文与计算材料见 [Graph](https://github.com/shouanrenhechun/Graph)。`C6BipartiteDomination/` 的源码保留原有版权声明与 Apache 2.0 许可，许可全文见 [LICENSE](LICENSE)。
