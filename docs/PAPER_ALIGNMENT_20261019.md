本轮实际核对与修订：14.02 分钟；累计：659.98 分钟。计至文件保存完成；后续仓库同步未加计。

# MOR34：论文—Lean 对应与外部结果边界

核对日期：2026-10-19。本文针对原稿 v0.1（2026-10-13）与修订稿 v0.2（2026-10-19），以及下列已验收的固定 Lean 源版本。

**结论：结构定理的数学结论一致；算法实现描述有差异，现已修改原文。主定理及参数依赖无需降低。算法层的形式化结论是对显式局部算法契约的条件定理，不是从零实现 ILP、精确秩和 Frank–Tardos 后得到的独立认证程序。**

## 1. 固定核对基准

- Lean 源提交：[`8951a2f5c5a64a477e907991b7653698d11ec440`](https://github.com/zac682210-commits/mor34_lean/tree/8951a2f5c5a64a477e907991b7653698d11ec440)。
- [成功的 CI：39146901961](https://github.com/zac682210-commits/mor34_lean/actions/runs/39146901961)，Lean 4.19.0；1154 个命名声明通过传递公理白名单审计。
- 原稿 PDF SHA256：`245e77fc9f9613ebb5ae1bfef7ae013412507002c3cac1b8eedb76d60b31645d`。修订前研究文件与仓库 reference 中的原稿逐字节相同，已据此修订。
- 修订稿 PDF SHA256：`bc1db82d40643e394d68d9eef74f46fccfc070735652ba84bcb37e5f953d4504`。正文与附录共 12 页；定理仍为 Lemmas 1–5、Corollary 6、Lemma 7、Theorem 8、Corollary 9。
- 本轮没有改 Lean 定义、定理、证明或工具链，不把文稿编辑后的提交冒充重新编译的源版本。

## 2. 符号与模型的准确对应

| 论文对象 | Lean 表示及对应解释 |
| --- | --- |
| 二进制向量 x | `Finset (Item m)` 或原始坐标 `Finset (Fin n)`；`pointVector`/`rawPointVector`给出实数指示向量。 |
| n,q,m_j | `n`；`q`或`RawNormalization.classes`；`m : Fin q → ℕ`。`WellFormed`要求非空系数类，所以 q≤n。 |
| a,b,c,d | 分组模型的`weight, capacity, coefficient, rhs`；部分顶层参数把c写为`v`。局部复杂度参数中同名的c不是候选系数向量。 |
| 正系数种数K | 原始候选系数值集合中严格正元素的个数；零值最多形成一个额外类，已证q≤K+1。 |
| 类内第r件物品/切口r | 物品下标为Lean的r−1；切口标号仍是r，分隔下标<r与≥r的物品。Lemma 4的区间无需整体平移。 |
| z∈Z⊂ℤ^q | `Counts q=Fin q→ℕ`，加`BoundedCounts`及紧前缀条件；与原文非负有界整数计数等价。ILP变量本身为ℤ。 |
| p(z)、T、A、C | `prefixSet`、`Tight`/`tightPointSet`、`componentCountMap`、`Fintype.card (ExchangeComponent P)`。 |
| 面维数 | 实数仿射张成的`vectorSpan`之`finrank`；空面由分支单独赋−1，不把空集的自然数维数误用为−1。 |
| 输出契约 | `RawOutput.Correct`：有效性、违反见证、空面、正确维数、facet布尔值、真实紧点基、仿射独立性、张成和基大小。 |
| 位长度L | 文中为通常输入长度；`rawIntegerPayload`是整数带符号位长之和，非具体文件序列化器；核心程序的`base.L`是系数大小≤2^L所用指数，不能与总长度直接混为同一变量。 |

`WellFormed`与原文假设一致：n≥1，正重量/正容量、每件物品重量≤容量、候选系数非负、类内重量非降。各结构引理未把“已经是facet”作为额外前提；需要facet的仅Corollary 6。计数的正系数种数、零系数类和原始标签均有桥接证明。

## 3. 逐项对应

以下链接固定到已通过 CI 的源提交，点开即为声明所在行。完整模块与声明清单在`paper_alignment_20261019.json`；每个列出的证明名都检查了源码存在性和`Check.lean`登记。

| 论文位置 | 形式化内容与边界 | 入口 |
| --- | --- | --- |
| §2 前缀最优性 | 同一类计数下前缀重量最小；计数、紧性保持。 | [`prefixMinimality`](https://github.com/zac682210-commits/mor34_lean/blob/8951a2f5c5a64a477e907991b7653698d11ec440/MOR34/PrefixMinimality.lean#L82)；[`counts_prefixSet`](https://github.com/zac682210-commits/mor34_lean/blob/8951a2f5c5a64a477e907991b7653698d11ec440/MOR34/PrefixMinimality.lean#L29)；[`prefix_tight`](https://github.com/zac682210-commits/mor34_lean/blob/8951a2f5c5a64a477e907991b7653698d11ec440/MOR34/PrefixMinimality.lean#L96) |
| Lemma 1，第3页 | 有理限制的语义编码及奇偶代换准确；实际算法的整数行构造和长度已证明。求解器本身见 E1。 | [`exact_linear_count_encoding`](https://github.com/zac682210-commits/mor34_lean/blob/8951a2f5c5a64a477e907991b7653698d11ec440/MOR34/LinearEncoding.lean#L103)；[`exact_parity_linear_count_encoding`](https://github.com/zac682210-commits/mor34_lean/blob/8951a2f5c5a64a477e907991b7653698d11ec440/MOR34/ParityLinearEncoding.lean#L27)；[`weightedRequests_solver_inputs`](https://github.com/zac682210-commits/mor34_lean/blob/8951a2f5c5a64a477e907991b7653698d11ec440/MOR34/WeightedDenseRequests.lean#L69) |
| Lemma 2，第3页 | 区间内所有交换边存在，连通分量为区间且由相邻边确定。 | [`intervalExchange`](https://github.com/zac682210-commits/mor34_lean/blob/8951a2f5c5a64a477e907991b7653698d11ec440/MOR34/Exchange.lean#L31)；[`connected_iff_cuts`](https://github.com/zac682210-commits/mor34_lean/blob/8951a2f5c5a64a477e907991b7653698d11ec440/MOR34/Components.lean#L97)；[`componentLabel_interval`](https://github.com/zac682210-commits/mor34_lean/blob/8951a2f5c5a64a477e907991b7653698d11ec440/MOR34/ExchangeKernel.lean#L139) |
| Lemma 3，第4页 | 交换空间等于 ker A；紧点与前缀的商像一致；非空紧面维数分解。 | [`exchangeDirectionSpan_eq_ker`](https://github.com/zac682210-commits/mor34_lean/blob/8951a2f5c5a64a477e907991b7653698d11ec440/MOR34/ExchangeKernel.lean#L96)；[`tight_image_eq_prefix_image`](https://github.com/zac682210-commits/mor34_lean/blob/8951a2f5c5a64a477e907991b7653698d11ec440/MOR34/PrefixQuotient.lean#L97)；[`tight_dimension_quotient`](https://github.com/zac682210-commits/mor34_lean/blob/8951a2f5c5a64a477e907991b7653698d11ec440/MOR34/TightDimension.lean#L61) |
| Lemma 4，第4–5页 | 完整奇偶向量相同；构造两个均跨指定切口的平分，并推出至少一个可行和相邻交换。 | [`balancedSplit`](https://github.com/zac682210-commits/mor34_lean/blob/8951a2f5c5a64a477e907991b7653698d11ec440/MOR34/BalancedSplit.lean#L7)；[`pairingAtCut`](https://github.com/zac682210-commits/mor34_lean/blob/8951a2f5c5a64a477e907991b7653698d11ec440/MOR34/PairingAtCut.lean#L5)；[`interiorExchange`](https://github.com/zac682210-commits/mor34_lean/blob/8951a2f5c5a64a477e907991b7653698d11ec440/MOR34/InteriorExchange.lean#L29)；[`parity_interior_connected`](https://github.com/zac682210-commits/mor34_lean/blob/8951a2f5c5a64a477e907991b7653698d11ec440/MOR34/Components.lean#L113) |
| Lemma 5，第5页 | 实际端点/中段区域上的商前缀映射仿射；覆盖、重复端点处理和 6^q 个索引。 | [`actual_cell_affine`](https://github.com/zac682210-commits/mor34_lean/blob/8951a2f5c5a64a477e907991b7653698d11ec440/MOR34/ParityCells.lean#L123)；[`parity_cell_cover`](https://github.com/zac682210-commits/mor34_lean/blob/8951a2f5c5a64a477e907991b7653698d11ec440/MOR34/ParityCells.lean#L135)；[`cellCondition_unique`](https://github.com/zac682210-commits/mor34_lean/blob/8951a2f5c5a64a477e907991b7653698d11ec440/MOR34/ParityCells.lean#L160)；[`cell_index_card`](https://github.com/zac682210-commits/mor34_lean/blob/8951a2f5c5a64a477e907991b7653698d11ec440/MOR34/ParityCells.lean#L171) |
| Corollary 6，第5页 | 对实际交换分量证明 C≤(3q+1)2^q，含原始输入的参数转换。 | [`facet_component_bound`](https://github.com/zac682210-commits/mor34_lean/blob/8951a2f5c5a64a477e907991b7653698d11ec440/MOR34/FacetComponentBound.lean#L71)；[`raw_facet_component_bound`](https://github.com/zac682210-commits/mor34_lean/blob/8951a2f5c5a64a477e907991b7653698d11ec440/MOR34/FacetComponentBound.lean#L89) |
| Lemma 7，第6页 | 增广法向量的有限构造、仿射基查询过程、每区域≤2(q+1)^2次调用和整数中间量界。 | [`computedCountForms_spec`](https://github.com/zac682210-commits/mor34_lean/blob/8951a2f5c5a64a477e907991b7653698d11ec440/MOR34/ExecutableCountForms.lean#L21)；[`linear_count_basis_correct`](https://github.com/zac682210-commits/mor34_lean/blob/8951a2f5c5a64a477e907991b7653698d11ec440/MOR34/LinearOracle.lean#L185)；[`linearBasisCalls_le`](https://github.com/zac682210-commits/mor34_lean/blob/8951a2f5c5a64a477e907991b7653698d11ec440/MOR34/LinearOracle.lean#L166)；[`preparedCellBasis_cost_on_states`](https://github.com/zac682210-commits/mor34_lean/blob/8951a2f5c5a64a477e907991b7653698d11ec440/MOR34/PreparedCellExecution.lean#L56) |
| Theorem 8 张成/维数，第6–8页 | 保留增广行张成整个紧点空间；有理秩=实秩；非空面维数=增广秩−1。 | [`selected_augmented_span`](https://github.com/zac682210-commits/mor34_lean/blob/8951a2f5c5a64a477e907991b7653698d11ec440/MOR34/SelectedSpan.lean#L49)；[`retained_row_span`](https://github.com/zac682210-commits/mor34_lean/blob/8951a2f5c5a64a477e907991b7653698d11ec440/MOR34/RetainedMatrix.lean#L43)；[`integer_matrix_rank`](https://github.com/zac682210-commits/mor34_lean/blob/8951a2f5c5a64a477e907991b7653698d11ec440/MOR34/RankScalar.lean#L50)；[`augmentedSpan_finrank`](https://github.com/zac682210-commits/mor34_lean/blob/8951a2f5c5a64a477e907991b7653698d11ec440/MOR34/AugmentedDimension.lean#L37) |
| Theorem 8 输出，第6–8页 | 无效时输出违反见证；空面返回−1；支持时返回正确维数、facet判定和真实紧点仿射基，恢复原标签。 | [`weightedNormalizedExecution_correct`](https://github.com/zac682210-commits/mor34_lean/blob/8951a2f5c5a64a477e907991b7653698d11ec440/MOR34/WeightedNormalizedExecution.lean#L42)；[`weightedRawExecution_correct`](https://github.com/zac682210-commits/mor34_lean/blob/8951a2f5c5a64a477e907991b7653698d11ec440/MOR34/WeightedRawExecution.lean#L21)；[`weightedRun_correct`](https://github.com/zac682210-commits/mor34_lean/blob/8951a2f5c5a64a477e907991b7653698d11ec440/MOR34/WeightedRunInterface.lean#L45) |
| Theorem 8 时间，第7–8页 | 同一返回值/费用执行的逐阶段组合，固定输入指数；经原始参数与预处理转换给出明确FPT界。依赖E1/E2/E4；压缩版本另依赖E3。 | [`weightedNormalizedExecution_cost`](https://github.com/zac682210-commits/mor34_lean/blob/8951a2f5c5a64a477e907991b7653698d11ec440/MOR34/WeightedNormalizedExecution.lean#L70)；[`weightedRun_sharp`](https://github.com/zac682210-commits/mor34_lean/blob/8951a2f5c5a64a477e907991b7653698d11ec440/MOR34/WeightedRunInterface.lean#L118)；[`complete_compressed_execution`](https://github.com/zac682210-commits/mor34_lean/blob/8951a2f5c5a64a477e907991b7653698d11ec440/MOR34/CompleteCompressedExecution.lean#L55) |
| Corollary 9，第8页 | 两次压缩的本题保持性质和大小；位复杂度与无原数值大小依赖的算术操作数分开。 | [`compression_output`](https://github.com/zac682210-commits/mor34_lean/blob/8951a2f5c5a64a477e907991b7653698d11ec440/MOR34/CompressionTransport.lean#L99)；[`compression_positive_parameter`](https://github.com/zac682210-commits/mor34_lean/blob/8951a2f5c5a64a477e907991b7653698d11ec440/MOR34/CompressionParameter.lean#L34)；[`compressed_payload_bound`](https://github.com/zac682210-commits/mor34_lean/blob/8951a2f5c5a64a477e907991b7653698d11ec440/MOR34/CompressionSize.lean#L36)；[`complete_strongly_polynomial_execution`](https://github.com/zac682210-commits/mor34_lean/blob/8951a2f5c5a64a477e907991b7653698d11ec440/MOR34/StrongPreparationCost.lean#L38) |

在这些入口中，`Targets.lean`、`PaperInterface.lean`只是冻结的初始命题规格。其头部保留的“OPEN/未编译”是初始检查点文字，不能据此判定当前进度，也不能把一个`Goal : Prop`定义算成证明。对应的实际证明在上表所列的`theorem`中。三份冻结文件保持不变。

## 4. 已修改原文的差异

| 原稿 v0.1 | Lean 验收路径 | v0.2 的处理及影响 |
| --- | --- | --- |
| §2、Theorem 8用二分搜索求极值 | 顺序扫描阈值并保留达到极值的见证 | 改为线性扫描；每一奇偶类求全部极值≤2(n+q)次调用。总FPT阶不变。 |
| Lemma 7从一个点出发，在差向量空间用消元取法向量 | 从空集出发，在(1,z)增广空间有限搜索枢轴/Cramer法向量 | 重写紧随Lemma 7的证明，加入空集、q+1个形式、两侧查询、每次增秩和完整候选检查。每区域≤2(q+1)^2次ILP调用。 |
| 法向量处只说消元和小子式界 | 枚举候选、Laplace行列式、检查所有原行，包含失败候选和中间和 | 补上系数界2(q+1)!(n+1)^(q+1)、候选数(q+2)(q+1)^(2(q+1))及q^{O(q)}构造成本。不得称该具体构造是关于q的纯多项式。 |
| 算法明确计算交换连通分量 | 执行只需相邻交换见证，A/分量用于张成证明 | 说明分量是证明对象，计算无需构造它；结构引理原样保留。 |
| 对全部方向/点的总矩阵求秩，然后提取基 | 保存前缀及每条成功边的两端紧点，反复做增秩检查 | 正文采用保留点族与具体增秩提取，说明方向矩阵R是张成证明工具。每次秩输入最多n+2行、n+1列；输出不变。 |
| 总查询数含2^q q log(n+1) | 支持性按奇偶扫描；极值用线性扫描 | 改为O(n+2^q(n+q+1)+6^q(q+1)^2)，参数化时间仍2^{O((K+1)log(K+2))}poly(n,L)。 |
| Lemma 1任意附加有理约束的“多项式编码长度”未说明基准 | 一般有理限制有语义编码；实际程序仅用受界整数附加行 | 补明还依赖附加约束自身编码长度；一般清分母成本属于基本算术结果，未声称其一般情形在实际整数构造代码中被验证。 |
| Corollary 9压缩后O(n^4)，计算模型较简略 | 两次调用、再归一化；普通位成本/强多项式算术成本两套局部契约 | 补明整数负载≤18(n+1)^4、保留原标签的基，以及“不依赖原数值大小”仅为算术操作数。 |

这些修改不改变原来的数学主张，只让读者看到与已核验参考执行相同的算法。二分搜索本身也可以成立，但它不是本次通过编译的执行路径，故不继续把它列为已验证实现。

## 5. 哪些既有结果没有在本项目内形式化

### E1．固定维整数线性可行性算法

**未形式化：**求解器存在性、内部正确性和维数 r 下 r^{O(r)} poly(B) 的复杂度定理。

**明确接口：**[`DenseRowSolverSpec`](https://github.com/zac682210-commits/mor34_lean/blob/8951a2f5c5a64a477e907991b7653698d11ec440/MOR34/DenseForcedSolver.lean#L9)；[`DenseSolverCostBound`](https://github.com/zac682210-commits/mor34_lean/blob/8951a2f5c5a64a477e907991b7653698d11ec440/MOR34/DenseSolverSize.lean#L12)。

**已有依据：**Lenstra–Frank–Tardos–Kannan；Bredereck et al., arXiv:1709.02850v2, Theorem 1。 [原文](https://arxiv.org/html/1709.02850v2)。

**本项目实际证明：**原始、奇偶、强制交换各类整数行的等价性、可行见证解码、2q 个有符号整数变量、实际输入大小、调用次数以及费用组合。

### E2．精确有理矩阵秩算法

**未形式化：**具体消元算法的实现、其正确性及多项式位复杂度；并未提供可运行的高效 ranker 实例。

**明确接口：**[`ExactIntegerRank`](https://github.com/zac682210-commits/mor34_lean/blob/8951a2f5c5a64a477e907991b7653698d11ec440/MOR34/NormalizedPipeline.lean#L9)；[`BinaryRankOperations`](https://github.com/zac682210-commits/mor34_lean/blob/8951a2f5c5a64a477e907991b7653698d11ec440/MOR34/ChargedBinaryRank.lean#L8)；[`BinaryRankBounds`](https://github.com/zac682210-commits/mor34_lean/blob/8951a2f5c5a64a477e907991b7653698d11ec440/MOR34/ChargedBinaryRank.lean#L25)。

**已有依据：**标准精确有理线性代数算法；本文只需整数矩阵上的有理秩。

**本项目实际证明：**输入矩阵确由保留的二进制点构成；插点增秩选择过程正确，次数/矩阵大小有界；Q 与 R 的秩相等、增广秩与仿射维数关系已在项目内证明。

### E3．Frank–Tardos 压缩定理

**未形式化：**压缩算法本身以及一般小符号保持、系数界、多项式位复杂度、强多项式算术操作数和预处理中间有理数位长保证。

**明确接口：**[`CompressionPrimitive`](https://github.com/zac682210-commits/mor34_lean/blob/8951a2f5c5a64a477e907991b7653698d11ec440/MOR34/ChargedCompressionPreparation.lean#L9)；[`PreparationLocalBounds`](https://github.com/zac682210-commits/mor34_lean/blob/8951a2f5c5a64a477e907991b7653698d11ec440/MOR34/ChargedCompressionPreparation.lean#L91)；[`PreparationStrongBounds`](https://github.com/zac682210-commits/mor34_lean/blob/8951a2f5c5a64a477e907991b7653698d11ec440/MOR34/StrongPreparationCost.lean#L8)。

**已有依据：**Frank–Tardos (1987)；Etscheid et al., arXiv:1507.03439v1, Theorem 1及其后说明。 [原文](https://arxiv.org/pdf/1507.03439)。

**本项目实际证明：**分别作用于 (a,b) 与 (c,d)，取 N=n+2；证明原假设、可行/紧点集、有效性、正系数类数 K 与输出保持，压缩整数负载 ≤18(n+1)^4，并组合两次调用和归一化代价。

### E4．基本算术、访问、排序和集合/矩阵构造算法

**未形式化：**本地操作的具体高效实现及其机器时间证明；任意附加有理行清分母的一般成本。

**明确接口：**[`IntegerArithmeticCharge`](https://github.com/zac682210-commits/mor34_lean/blob/8951a2f5c5a64a477e907991b7653698d11ec440/MOR34/WeightedIntegerEvaluation.lean#L7)；[`CountMatrixPreparation`](https://github.com/zac682210-commits/mor34_lean/blob/8951a2f5c5a64a477e907991b7653698d11ec440/MOR34/PreparedNormalExecution.lean#L9)；[`PointOperations`](https://github.com/zac682210-commits/mor34_lean/blob/8951a2f5c5a64a477e907991b7653698d11ec440/MOR34/ChargedRecognitionExecution.lean#L43)；[`PointOperationBounds`](https://github.com/zac682210-commits/mor34_lean/blob/8951a2f5c5a64a477e907991b7653698d11ec440/MOR34/ChargedRecognitionExecution.lean#L55)；[`NormalizationPrimitive`](https://github.com/zac682210-commits/mor34_lean/blob/8951a2f5c5a64a477e907991b7653698d11ec440/MOR34/ChargedCompressionPreparation.lean#L16)；[`RelabelLocalBounds`](https://github.com/zac682210-commits/mor34_lean/blob/8951a2f5c5a64a477e907991b7653698d11ec440/MOR34/ChargedRawExecution.lean#L65)；[`ExecutionLocalBounds`](https://github.com/zac682210-commits/mor34_lean/blob/8951a2f5c5a64a477e907991b7653698d11ec440/MOR34/CompleteReferenceApplication.lean#L7)；[`WeightedExecutionLocalBounds`](https://github.com/zac682210-commits/mor34_lean/blob/8951a2f5c5a64a477e907991b7653698d11ec440/MOR34/CompleteWeightedApplication.lean#L34)。

**已有依据：**标准多项式时间整数算术、比较、有限数组/集合处理及排序；常数和多项式次数在参数 q 之前固定。

**本项目实际证明：**具体值规范与算法输出一致；实际整数表达式、法向量候选及中间和的位长、调用所在阶段、次数和合成费用。实际识别路径只构造整数行。

一般固定维ILP定理输入若规定变量非负，2q个有符号变量需作标准正负部分转换，维数可到4q；始终是O(q)，不影响最终参数阶。论文已明确2q是自身有符号 formulation 的变量数，而不是对所有外部求解器输入格式的承诺。

### 5.1 “无自定义公理”不等于“没有算法假设”

最终定理的逻辑形态是：对满足标准局部规范及费用界的原语，证明本题组合程序的输出正确和总费用界。形式上为`local_contracts → correctness ∧ cost_bound`。Lean检验了这一蕴含，尚未在Lean中构造满足全部复杂度要求的ILP、rank与FT实现。因此“独立可运行的高效完整认证求解器”不在完成范围内。E1–E4是公开可审查的参数/假设，不能因`#print axioms`没有额外公理而忽略。

对位复杂度，标准原语存在性与其局部成本由外部算法定理提供。原语次数、其实际输入与大小、原语所处递归状态、各阶段费用求和、参数依赖和固定输入指数由本项目推导；没有把最终核心程序的总时间上界作为假设。

### 5.2 哪些既有数学是已经形式化、直接复用的

Mathlib中的有限维线性代数、秩—零化度、仿射/凸包、行列式恒等式、有限集与整数代数属于已经存在的形式化证明，固定依赖版本为`c44e0c8ee63ca166450922a373c7409c5d26b00b`。它们不应列入“未形式化”。

项目还亲自写出了若干标准结论的适配证明：整数矩阵Q/R秩桥接（`integer_matrix_rank`）、非空点集的增广秩/仿射维数桥接（`augmentedSpan_finrank`）、具体凸前缀的epigraph等价性。因此，不能笼统说“线性代数没形式化”或“epigraph没形式化”；缺少的是外部高效算法实现/复杂度的内部认证，而不是这些代数事实。

### 5.3 其他未认证内容

- 引言引用的Chen–Zhu DP-completeness及XP算法、历史归属与新颖性检索：属于背景，不是本次Lean证明对象。
- 第6节六物品例子：保留解析说明和原Python检查，未单独成为Lean实例定理。
- Lean编译器/后端的机器运行语义、操作数收费与机器指令时间的完全对应、真实机器性能：不在本次验收范围。
- 人工确认PDF表述与Lean类型等价：本报告逐项完成了对应审阅，但Lean不会自动读取PDF并证明翻译忠实性。

## 6. 获取并重建修订稿

修订稿的英文附录A（第9–11页）已包含模型对应、三张编号表、主要入口和上述外部依赖边界。原研究PDF与复现ZIP更新到v0.2，既有研究/实验文件保留，Python程序没有因文稿修订而重新运行或产生新的实验统计。

仓库`reference/mor34_fpt_proof.tex/pdf`作为已验收源版本的v0.1快照保持原样。版本0.2由补丁精确重建：

```sh
mkdir -p /tmp/mor34-paper-v02
patch -o /tmp/mor34-paper-v02/mor34_fpt_proof.tex reference/mor34_fpt_proof.tex < reference/mor34_v0.2.patch
cd /tmp/mor34-paper-v02
pdflatex -interaction=nonstopmode -halt-on-error mor34_fpt_proof.tex
pdflatex -interaction=nonstopmode -halt-on-error mor34_fpt_proof.tex
```

补丁重建的TeX已与交付TeX逐字节比对；PDF需依编译时间/发行版允许元数据差异。原稿与修订稿的哈希、页码、声明名和固定源链接记录于`paper_alignment_20261019.json`。本次没有重新更改证明目标或隐去标准算法假设。
