[English](README.md) | [简体中文](README_zh.md)

# Lean 4 中的高维 Erdős 不同距离下界

对每个固定维数 `d ≥ 3`，`ℝ^d` 中任意 `n` 点集至少确定 `c_d · n^(2/d)` 个不同距离，其中 `c_d > 0` 是某个常数；并且这个阶是最优的：对每个 `n ≥ 2`，存在某个 `n` 点集至多确定 `C_d · n^(2/d)` 个不同距离。

- **作者：** Yao Xu ([@cadamcat](https://github.com/cadamcat))；见[作者与署名说明](AUTHORS.md)。
- **数学结果：** OpenAI，[*The higher-dimensional Erdős distinct-distances conjecture*](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-higher-dimensional-Erdos-distinct-distances-conjecture-September-23-2026/paper.pdf)，定理 `thm:main`（以及引言中与之匹配的网格上界）。
- 本项目在 AI 协助下开发；所有证明均由 Lean 4 内核验证。

## 主要结果

本仓库证明 [Challenge.lean](Challenge.lean) 中陈述的如下定理：

```lean
namespace DistinctDistances

theorem jsp_000900 :
    ∀ d : ℕ, 3 ≤ d →
      ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
        (∀ P : Finset (EuclideanSpace ℝ (Fin d)), 2 ≤ P.card →
          c * (P.card : ℝ) ^ ((2 : ℝ) / (d : ℝ)) ≤ (distinctDistances P : ℝ)) ∧
        (∀ n : ℕ, 2 ≤ n → ∃ P : Finset (EuclideanSpace ℝ (Fin d)), P.card = n ∧
          (distinctDistances P : ℝ) ≤ C * (n : ℝ) ^ ((2 : ℝ) / (d : ℝ)))
```

`distanceSet P` 是 `P` 中所有非对角点对的距离 `dist p q` 组成的有限集，`distinctDistances P` 是它的元素个数。点位于 `EuclideanSpace ℝ (Fin d)` 中；幂为实数幂（`Real.rpow`）。下界对至少含两个点的每个有限点集成立；上界对每个 `n ≥ 2` 由某个 `n` 点集（整数网格的子集）实现，因此指数 `2/d` 是精确的；本仓库不声称精确的首项常数。

[Challenge.lean](Challenge.lean) 包含这一陈述及其所用定义，均复制自 Formal Conjectures，且只导入 Mathlib。[DistinctDistances/Defs.lean](DistinctDistances/Defs.lean) 是证明所用定义的逐字副本。[DistinctDistances/Main.lean](DistinctDistances/Main.lean) 由下界部分（`lower_bound`，track E）和上界部分（`upper_bound`）证明一个同名、同陈述的定理。[Challenge.json](Challenge.json) 配置 Comparator 对这两个模块进行比较。[docs/verification.md](docs/verification.md) 说明陈述检查以及与 Formal Conjectures 文件的差异。

## 证明的组织

形式证明沿用论文的结构。OpenAI 的 Lean 库提供多项式隔离接口（距离问题的物理分隔器和隔离多项式）。本仓库形式化论文的其余部分：多项式方法、关联与直纹几何、运动与平面输入、曲线与秩的桥接、割线/划分的组装，以及得出下界的最终归纳，并给出匹配上界的网格构造。

| 路径 | 内容 |
| --- | --- |
| `DistinctDistances/Defs.lean` | 证明所用 Formal Conjectures 定义的逐字副本 |
| `DistinctDistances/Upper.lean` | `upper_bound`：给出 `C · n^(2/d)` 个距离的网格构造 |
| `DistinctDistances/Framework/` | 失败情形、渐近计数记号、对角归纳的设置 |
| `DistinctDistances/Foundations/` | 共用的几何模型：仿射与射影簇、局部代数、投影 |
| `DistinctDistances/TrackA/` | 多项式方法：Bézout 界、插值、Hilbert 估计、正则性、压缩、投影 |
| `DistinctDistances/TrackB/` | 关联几何：Segre 数据、斜线束、零刚性、关联 Hilbert 界、细化 |
| `DistinctDistances/TrackC/` | 运动与平面输入：富运动、弱平面界、典范梯度 |
| `DistinctDistances/Bridges/` | 各 track 之间的曲线、分支、秩和直线桥接 |
| `DistinctDistances/TrackD/` | 割线、切线与划分的组装 |
| `DistinctDistances/TrackE/` | 最终组装：共同输入，以及对 `d ≥ 3` 作强归纳得到的 `lower_bound` |
| `DistinctDistances/Main.lean` | `DistinctDistances.jsp_000900` |
| `Audit/TargetProbes.lean`、`Audit/IndependentRestatement.lean` | 对目标定义的内核检查探针，以及把距离计数显式写出的目标重述，并证明其与原陈述等价 |

## 构建与验证

环境要求：Git、Python 3 和 [elan](https://github.com/leanprover/elan)，并确保 `lake` 已加入 `PATH`。在全新检出版本的仓库根目录运行：

```sh
lake update
scripts/apply-oai-patches.sh
lake exe cache get
lake build
```

OpenAI 的 `lake update` hook 会在解析依赖并写入 `lake-manifest.json` 后报错，错误以 `iut: Lake resolved an unexpected checkout at …` 开头。随后运行补丁脚本；它会把 OpenAI 的 Lean 4.34.1 兼容补丁应用到已获取的依赖包，也可在再次运行 `lake update` 后重新运行。

若要检查冻结的陈述、定义、公理以及是否含有禁用构造，请运行：

```sh
LEAN_NUM_THREADS=4 ./scripts/verify.sh
```

该脚本构建 `DistinctDistances.Main`，检查 `Challenge.lean` 与其冻结版本一致，检查 `DistinctDistances.jsp_000900` 的定义和展开后的陈述与 `Challenge.lean` 一致，检查该定理只依赖 `propext`、`Classical.choice` 和 `Quot.sound`，并扫描仓库中每个 Lean 源文件，查找 `sorry`、`admit`、新增公理、`native_decide`、`implemented_by`、`extern` 和 unsafe 代码。全部检查通过时以状态码 0 退出；证明仍依赖 `sorryAx` 时以 2 退出；其他失败以 1 退出。`./scripts/replay.sh` 在全新的 Lean 内核环境中重放该定理所在模块及其导入的全部内容。[docs/verification.md](docs/verification.md) 说明每项检查和 Comparator 配置。

## 固定依赖

- Lean `v4.34.1`，由 [lean-toolchain](lean-toolchain) 选定。
- [Mathlib](https://github.com/leanprover-community/mathlib4)，提交 `d13f23b723b8a846827a245b89c10fc7d3f11612`。
- OpenAI 的 [`openai/math`](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean)，提交 `adc7f1241b42e322a6451854ab7e4b4c146bf78a`。
- 其余依赖版本由 OpenAI 的库固定，见 [lake-manifest.json](lake-manifest.json)。

## 数学参考文献

- OpenAI，[*The higher-dimensional Erdős distinct-distances conjecture*](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-higher-dimensional-Erdos-distinct-distances-conjecture-September-23-2026/paper.pdf)，2026 年 9 月 23 日。
- P. Erdős，[On sets of distances of `n` points](https://www.renyi.hu/~p_erdos/1946-03.pdf)，*American Mathematical Monthly* 53 (1946)，248–250。平面情形的猜想阶不同。

## 许可证

Apache-2.0；见 [LICENSE](LICENSE)、[NOTICE](NOTICE) 和[第三方署名说明](THIRD_PARTY.md)。
