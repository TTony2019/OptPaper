# Lean 形式化与论文内容对照

论文：*A Dynamical Approach to an Inertial Forward-Backward Algorithm for Convex Minimization*（Attouch--Peypouquet--Redont, 2014）  
论文文本：[todo/Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014.md](/home/liyantao/Paper2Lean/todo/Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014.md)  
形式化目录：[items](/home/liyantao/Paper2Lean/theorem_lib/TheoremLib/Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014/items)

## 结论摘要

- 主线数学内容已经覆盖：IFB 算法、能量与 Liapunov 序列、命题 2/3/4/6/8/12、引理 5/7/13、定理 1、推论 9--11，以及梯度投影、CQ、ISTA 和 IFB 信号恢复应用。
- `def_2`--`def_9`、`algo_1`、`prop_1`--`prop_5`、`cor_1`、`cor_3` 的核心公式/结论，在把 Lean 的索引证明参数和 `EReal` 表示展开后，与论文相同或等价。
- 存在三类需要注明的差异：
  1. 为了 Lean 类型和现有基础库，某些结果增加了前提（`cor_2` 的最小值存在性、`prop_6` 的连续性、`lem_3` 的有界性等）；
  2. 应用算法定义有意省略了论文中的线性、连续、权重归一化和步长限制，因此这些定义本身比论文算法更宽；
  3. 论文中的“相对紧”在 `def_10`/`cor_3` 中写成了“闭包紧”，在赋范空间中这是等价表述。

下文的“等价”指：在论文相同的数学假设下，忽略证明无关的 Lean witness（例如 `1 ≤ k` 的证明）后，陈述可相互改写；“偏弱/偏强”只针对该 Lean 声明本身的前提或结论。

## 1. 假设、定义和主算法

| Lean 文件与声明 | 论文位置 | 对照结论 |
|---|---|---|
| [`def_1.lean:7`](/home/liyantao/Paper2Lean/theorem_lib/TheoremLib/Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014/items/def_1.lean:7) `IFBHypothesis`：`Phi` proper/lsc/convex，`Psi` 可微且梯度 `Lpsi`-Lipschitz，`a,b,lambda>0`，步长上界，`Theta=Phi+Psi` convex 且有下界。 | 第 2 节 Hypothesis H，论文行 122--132。 | 等价编码。Lean 用 `Convex ℝ (epigraph f)` 和闭 epigraph 表示凸性/lsc；`Lpsi>0` 没有作为字段，但由正步长和严格步长上界推出。 |
| [`algo_1.lean:10`](/home/liyantao/Paper2Lean/theorem_lib/TheoremLib/Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014/items/algo_1.lean:10) `IsIFBTrajectory`：存在 `g∈∂Phi(u_{k+1})` 使第一更新为 0，第二更新为 0。 | (IFB)，论文行 88--94，公式行 90--92。 | 等价。`0∈...` 被写成“存在次梯度元素且向量等于 0”；Lean 将 `a,b,lambda>0` 和 `Phi` proper 放在轨迹结构中。 |
| [`def_2.lean:7`](/home/liyantao/Paper2Lean/theorem_lib/TheoremLib/Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014/items/def_2.lean:7) `gamma=(1-a*lambda)/(2*b*lambda^2)`；`gamma_pos`。 | (3.1)，论文行 153--157。 | 定义等价；正性定理是论文中“由 `H_lambda` 得到”的显式 Lean 引理。 |
| [`def_3.lean:6`](/home/liyantao/Paper2Lean/theorem_lib/TheoremLib/Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014/items/def_3.lean:6) `velocity u k = u k-u(k-1)`。 | `xi_k`，(3.2) 前，论文行 159--163。 | 等价，但 Lean 只对 `k>=1` 定义/使用，并把该条件作为 proof 参数。 |
| [`def_5.lean:6`](/home/liyantao/Paper2Lean/theorem_lib/TheoremLib/Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014/items/def_5.lean:6) `zeta y k = y k-y(k-1)`。 | (3.3)，论文行 173--175。 | 等价，同样只在正索引使用。 |
| [`def_6.lean:11`](/home/liyantao/Paper2Lean/theorem_lib/TheoremLib/Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014/items/def_6.lean:11) `zSequence=xi/lambda+a*u(k-1)-b*y(k-1)`；`HasZSubgradient` 要求 `-z_k∈∂Phi(u_k)`。 | (3.4)，论文行 177--181。 | 等价。论文把定义和次梯度归属写在同一行，Lean 分成 `zSequence` 与谓词。 |
| [`def_4.lean:8`](/home/liyantao/Paper2Lean/theorem_lib/TheoremLib/Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014/items/def_4.lean:8) `mechanicalEnergy=Theta(u_k)+gamma*||xi_k||^2`。 | (3.2)，论文行 165--169。 | 等价（值域用 `EReal`，平方项由 `ℝ` 嵌入）。 |
| [`def_7.lean:8`](/home/liyantao/Paper2Lean/theorem_lib/TheoremLib/Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014/items/def_7.lean:8) `auxiliaryG`：`<z_k,u_k-q>-sum_{i=2}^k <z_i,xi_i>`，并限制 `k>=2`。 | (3.11)，论文行 281--285。 | 等价；`Finset.Icc` 加 `attach` 只是依赖证明索引的实现。 |
| [`def_8.lean:8`](/home/liyantao/Paper2Lean/theorem_lib/TheoremLib/Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014/items/def_8.lean:8) `liapunovF`，含 `alpha=(1+b*lambda)/(2*lambda^2)`、`delta=(2+(b-a)*lambda)/(2*lambda^2)`。 | (3.12)，论文行 287--297。 | 等价；论文的 `G_{k+1}`、`sum_{i=2}^k` 用 Lean 的显式索引证明实现。 |
| [`def_9.lean:7`](/home/liyantao/Paper2Lean/theorem_lib/TheoremLib/Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014/items/def_9.lean:7) `auxiliaryA`。 | (3.23)，论文行 484--488。 | 等价。 |

## 2. 能量分析和渐近命题

| Lean 文件与声明 | 论文位置 | 对照结论 |
|---|---|---|
| [`prop_1.lean:105`](/home/liyantao/Paper2Lean/theorem_lib/TheoremLib/Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014/items/prop_1.lean:105) `proposition2`：能量从 `E_{k+1}` 到 `E_{k+2}` 非增，`sum ||u_{k+1}-u_k||^2` 可和，能量与目标值趋于同一 `EReal` 极限。 | PROPOSITION 2，论文行 183--186；证明中的 (3.5)--(3.10)。 | 等价。Lean 用 `k+1/k+2` 避开 `xi_0` 未定义；论文“`(||xi_k||)∈ell^2`”被写成平方范数级数可和。`proposition2_beta_pos`（:17）是对 (3.10) 正性的单独证明，不是新增论文结论。 |
| [`prop_2.lean:439`](/home/liyantao/Paper2Lean/theorem_lib/TheoremLib/Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014/items/prop_2.lean:439) `proposition3`：凸 `Theta` 下，(3.13) 的上界、`b<...>=F_{k+1}-F_k` 恒等式，以及 `q∈Argmin Theta` 时 `F` 非增。 | PROPOSITION 3，论文行 301--309；公式 (3.13)--(3.17)。 | 等价。 |
| [`prop_3.lean:547`](/home/liyantao/Paper2Lean/theorem_lib/TheoremLib/Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014/items/prop_3.lean:547) `proposition4`：对 `q∈dom(Phi)`，`G_k(q)`（`k>=2`）存在统一上界。 | PROPOSITION 4，论文行 365--399；(3.18)--(3.21)。 | 等价。Lean 将上界常数显式构造为一个 `ℝ` 表达式，并使用 Proposition 2 的平方可和性。 |
| [`lem_1.lean:68`](/home/liyantao/Paper2Lean/theorem_lib/TheoremLib/Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014/items/lem_1.lean:68) `lemma5`：三条递推条件和 `epsilon` 可和推出 `theta>=0`。 | LEMMA 5，论文行 418--432。 | 等价。Lean 加 `1<=k_0`，因为形式化递推显式出现 `k-1`；论文只说“从某个足够大的索引起”。`Σ ||epsilon_k||` 是实数绝对可和。 |
| [`prop_4.lean:712`](/home/liyantao/Paper2Lean/theorem_lib/TheoremLib/Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014/items/prop_4.lean:712) `proposition6`：`Theta(u_k)->sInf(range Theta)`；每个弱序列聚点在 `Argmin Theta`；若 `Argmin Theta=empty` 则 `||u_k||->infinity`。 | PROPOSITION 6，论文行 434--456。 | 等价。Lean 把弱收敛写成 `toWeakSpace` 中的序列聚点，把 `inf Theta` 写成 `sInf (Set.range Theta)`，并显式要求 `[CompleteSpace H]`。 |
| [`lem_2.lean:21`](/home/liyantao/Paper2Lean/theorem_lib/TheoremLib/Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014/items/lem_2.lean:21) `lemma7`：非负序列满足最终的 `p_k-omega*p_{k-1}<=K` 且 `omega<1` 时有界。 | LEMMA 7，论文行 460--468。 | 等价；“最终成立”用 `exists k_0, forall k>=k_0` 表示。 |
| [`prop_5.lean:151`](/home/liyantao/Paper2Lean/theorem_lib/TheoremLib/Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014/items/prop_5.lean:151) `proposition8`：`Argmin Theta` 非空时 `range u` 有界，且每个最小点 `q` 对应的 `F_k(q)` 有实极限。 | PROPOSITION 8，论文行 470--478。 | 等价。 |
| [`thm_1.lean:1120`](/home/liyantao/Paper2Lean/theorem_lib/TheoremLib/Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014/items/thm_1.lean:1120) `theorem1`：目标值趋于下确界；在 Argmin 非空且满足单点、`Phi` 可微、`gradPsi` 弱到弱连续或 `Psi` 凸之一时，`u_k` 弱收敛到最小点；无最小点时范数发散。 | THEOREM 1，论文行 140--151，定理陈述行 142--149。 | 语义等价。论文条件 (ii)“`Phi` 可微”在 Lean 中展开成全局实值代表 `phiReal`、`Differentiable`、梯度表示及弱到弱连续性；这是同一条件的显式类型化。Lean 文件中的 `theorem1_proposition8_local` 等局部重建只修复 `liapunovF` 的 proof-index，不改变定理语义。 |

## 3. 强收敛和辅助序列

| Lean 文件与声明 | 论文位置 | 对照结论 |
|---|---|---|
| [`cor_1.lean:29`](/home/liyantao/Paper2Lean/theorem_lib/TheoremLib/Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014/items/cor_1.lean:29) `corollary9`：有限维、`Argmin Theta` 非空时存在最小点 `q`，且 `u_k` 强收敛到 `q`。 | COROLLARY 9，论文行 588--590。 | 等价。有限维完备性和弱拓扑到原拓扑的连续逆由 Lean 实例/辅助引理提供。文件前面的 `ifb_lipschitz_constant_pos`（:15）是证明工具。 |
| [`cor_2.lean:64`](/home/liyantao/Paper2Lean/theorem_lib/TheoremLib/Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014/items/cor_2.lean:64) `corollary10`：强凸时强收敛到某个最小点。 | COROLLARY 10，论文行 592--606。 | 结论相同，但 Lean **增加了** `(Argmin Theta).Nonempty` 前提。论文直接由 proper/lsc/强凸等假设使用唯一最小点；Lean 注释中的 TODO 说明当前基础库尚未自动证明最小值取得。因此这是“附加存在性假设下等价”，不是字面等价。 |
| [`def_10.lean:7`](/home/liyantao/Paper2Lean/theorem_lib/TheoremLib/Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014/items/def_10.lean:7) `IsBoundedlyInfCompact`：所有 `r`、`R>0` 的下水平集与球的闭包紧。 | 第 4.1.3 节，论文行 608--612。 | 等价。在赋范/Hausdorff 空间，“集合相对紧”等价于“其闭包紧”。 |
| [`cor_3.lean:10`](/home/liyantao/Paper2Lean/theorem_lib/TheoremLib/Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014/items/cor_3.lean:10) `corollary11`：弱收敛加 boundedly inf-compact 得强收敛，极限属于 Argmin。 | COROLLARY 11，论文行 614--618。 | 等价；Lean 把“弱收敛”作为显式 `Tendsto` 前提，并分别返回强极限和最小性。 |
| [`prop_6.lean:64`](/home/liyantao/Paper2Lean/theorem_lib/TheoremLib/Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014/items/prop_6.lean:64) `proposition12`：若 `u_k` 弱收敛且梯度弱到弱连续，则 `y_k` 弱收敛；若 `u_k` 强收敛则 `y_k` 强收敛；极限满足 `gradPsi uLim-a*uLim+b*yLim=0`。 | PROPOSITION 12，论文行 620--637，(4.2)--(4.5)。 | 结论等价，但 Lean 整个声明额外要求 `hgrad_cont : Continuous gradPsi`。论文的 (ii) 在 Hypothesis H 下可由 Lipschitz 梯度得到连续性，Lean 因该定理不接收 `hH` 而把它作为显式前提，所以是偏强接口。 |
| [`lem_3.lean:71`](/home/liyantao/Paper2Lean/theorem_lib/TheoremLib/Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014/items/lem_3.lean:71) `lemma13`：`p_{k+1}<=eta*p_k+epsilon_k`、`0<eta<1`、`limsup epsilon<=0` 推出 `limsup p<=0`。 | LEMMA 13，论文行 639--667。 | 结论相同，但 Lean **增加了** `Filter.IsBoundedUnder (·<=·) atTop epsilon`。这可能由某些 `limsup` 事实推出，但在当前声明中没有推导，因此按接口比较属于偏强。文件中的 `eventually_lt_of_contract_recurrence`（:5）和 `limsup_le_zero_of_eventually_lt_pos`（:54）是证明辅助定理，不是论文新增结果。 |

## 4. 梯度投影、CQ 和信号恢复应用

| Lean 文件与声明 | 论文位置 | 对照结论 |
|---|---|---|
| [`algo_2.lean:9`](/home/liyantao/Paper2Lean/theorem_lib/TheoremLib/Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014/items/algo_2.lean:9) `IsGradientProjectionTrajectory`：`mu=lambda/(1+lambda)`，`u_{k+1}=Proj_C(lambda*y_k+(1-lambda)*u_k)`，`y_{k+1}=(1-mu)y_k+mu(u_{k+1}-gradPsi(u_{k+1}))`。 | (5.1)，论文行 713--720。 | 更新公式等价。`projectionPoint` 配合 `IsChebyshev C` 是投影的函数化表示；该定义本身没有重复写出论文后面用于收敛的步长上界。 |
| [`algo_3.lean:8`](/home/liyantao/Paper2Lean/theorem_lib/TheoremLib/Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014/items/algo_3.lean:8) `IsClassicalGradientProjectionTrajectory`：`u_{k+1}=Proj_C((1-lambda)u_k+lambda*sum omega_i Proj_{C_i}(u_k))`，`0<lambda<2`。 | (5.4)，论文行 754--762。 | 迭代公式相同，但 Lean 没有要求论文中的 `omega_i>0`、`sum omega_i=1`，也没有显式表达各集合非空闭凸（只接收 `IsChebyshev`）。因此定义比论文应用设定更宽。 |
| [`algo_4.lean:9`](/home/liyantao/Paper2Lean/theorem_lib/TheoremLib/Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014/items/algo_4.lean:9) `IsGeneralIFBGradientProjection`：一般 `a,b` 的两步投影/惯性更新。 | (5.6)，论文行 790--806，公式行 790--794。 | 公式等价，但 Lean 只在每个 `k` 要求 `a,b>0`，没有要求 `lambda>0` 或 `lambda<min{1/a,2(a+b)/(bL)}`，也没有权重正性/归一化。因此作为“算法关系”明显比论文的收敛假设更宽。 |
| [`algo_5.lean:10`](/home/liyantao/Paper2Lean/theorem_lib/TheoremLib/Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014/items/algo_5.lean:10) `IsCQTrajectory`：`Proj_C(u_k-lambda*A^t(Au_k-Proj_Q(Au_k)))`。 | CQ 算法 (5.13)，论文行 810--856，公式行 850--854。 | 更新公式等价。Lean 的 `_hAt` 只规定内积伴随关系，没有把 `A`、`At` 声明为线性连续算子，也没有把 `lambda<2/rho(A^tA)` 放进定义；所以定义域比论文更宽，论文的收敛结论不能仅从该谓词推出。 |
| [`algo_6.lean:11`](/home/liyantao/Paper2Lean/theorem_lib/TheoremLib/Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014/items/algo_6.lean:11) `IsIFBCQTrajectory`：(5.14) 的 IFB-CQ 两步更新。 | (5.14)，论文行 858--870，公式行 860--862。 | 公式等价；Lean 要求 `a,b,lambda>0`，但仍缺少 `A`/`At` 线性连续性和 `lambda` 的 `Lambda` 上界，故整体接口比论文应用假设更宽。 |
| [`algo_7.lean:7`](/home/liyantao/Paper2Lean/theorem_lib/TheoremLib/Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014/items/algo_7.lean:7) `IsISTATrajectory`：`u_{k+1}=prox(u_k-2*lambda*At(Au_k-data))`，并用 `f(v)=lambda*gamma*sum |v_i|` 和 `IsProxPoint` 描述软阈值近端。 | ISTA (5.18)，论文行 906--942，公式行 938--942；近端显式式 (5.16)--(5.17)。 | 迭代形式等价：论文的 `prox_{lambda*gamma||.||_1}` 被 Lean 编码为函数 `prox` 对应的 `f`。Lean 没有要求 `A!=0`、`A` 为矩阵/线性连续、`At` 真为线性伴随（只有内积恒等式），所以应用设定较宽；同时没有把 `lambda,gamma>0` 写进谓词。 |
| [`algo_8.lean:8`](/home/liyantao/Paper2Lean/theorem_lib/TheoremLib/Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014/items/algo_8.lean:8) `IsIFBSignalRecoveryTrajectory`：`u` 的近端 IFB 更新和 `y` 的 `At(Au-data)` 更新。 | IFB 信号恢复 (5.19)，论文行 944--956，公式行 946--948。 | 公式等价；同样缺少论文中 `A` 的矩阵/线性非零性质、参数正性和步长限制。`f= lambda*gamma*||.||_1` 的表达与 (5.19) 的 `prox_{lambda gamma ||.||_1}` 一致。 |

## 5. 外部定义、定理和备注项

这些文件主要把公共基础库中的概念引入论文命名空间，或提供论文证明用的标准工具；它们没有独立改变论文命题。

| 文件 | 引入内容 | 论文对应部分 | 判断 |
|---|---|---|---|
| [`ext_def_1.lean:6`](/home/liyantao/Paper2Lean/theorem_lib/TheoremLib/Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014/items/ext_def_1.lean:6) | `Optimization.argminSet` | 定理 1、命题 6/8、推论 9--11 中的 `S=Argmin Theta`（论文行 142--149、436--470） | 标准定义，等价。 |
| [`ext_def_2.lean:6`](/home/liyantao/Paper2Lean/theorem_lib/TheoremLib/Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014/items/ext_def_2.lean:6) | `ERealFunction.subdifferential` | (IFB)、(3.4)、(3.14) | 标准凸次微分。 |
| [`ext_def_3.lean:6`](/home/liyantao/Paper2Lean/theorem_lib/TheoremLib/Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014/items/ext_def_3.lean:6) | `IsWeakToWeakSequentiallyContinuous` | 定理 1 条件 (ii)/(iii)，命题 12 | 标准弱到弱序列连续性。 |
| [`ext_def_4.lean:6`](/home/liyantao/Paper2Lean/theorem_lib/TheoremLib/Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014/items/ext_def_4.lean:6) | `IsStronglyConvexWith` | 第 4.1.2 节、推论 10（论文行 592--606） | 标准强凸性谓词。 |
| [`ext_def_5.lean:5`](/home/liyantao/Paper2Lean/theorem_lib/TheoremLib/Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014/items/ext_def_5.lean:5) | `proximityOperator`、`IsProxPoint` | 近端重写 (2.1)，以及 (5.16)--(5.19) | 标准近端定义/图像谓词。 |
| [`ext_def_6.lean:6`](/home/liyantao/Paper2Lean/theorem_lib/TheoremLib/Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014/items/ext_def_6.lean:6) | `setValuedProjector`、Chebyshev 投影定理 | 第 5.1 节梯度投影和 CQ（论文行 713--870） | 将集合值投影函数化；公式层面等价。 |
| [`ext_def_7.lean:8`](/home/liyantao/Paper2Lean/theorem_lib/TheoremLib/Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014/items/ext_def_7.lean:8) | `indicatorFunction` | `Phi=delta_C`，第 5.1 节 | 标准指标函数。 |
| [`ext_def_8.lean:6`](/home/liyantao/Paper2Lean/theorem_lib/TheoremLib/Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014/items/ext_def_8.lean:6) | `distanceToSet x C=sInf_{v in C} dist(x,v)` | (5.2)、(5.3)、(5.9) 的距离惩罚，论文行 738--752、824--833 | 对非空 `C` 与通常距离定义等价；空集时取 `sInf empty` 的扩展实数值，论文未讨论该退化情形。 |
| [`ext_thm_1.lean:5`](/home/liyantao/Paper2Lean/theorem_lib/TheoremLib/Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014/items/ext_thm_1.lean:5) | `opial_lemma` | 定理 1 证明末段（论文行 480--582） | 直接使用 Opial 引理，语义一致。 |
| [`ext_thm_2.lean:6`](/home/liyantao/Paper2Lean/theorem_lib/TheoremLib/Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014/items/ext_thm_2.lean:6) | `descent_lemma`：Lipschitz 梯度的下降不等式 | (3.6)，论文行 207--223 | 结论与论文使用的 descent lemma 一致。 |
| [`rem_1.lean:8`](/home/liyantao/Paper2Lean/theorem_lib/TheoremLib/Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014/items/rem_1.lean:8) `remark15` | `Psi` 凸时调用定理 1 的条件 (iv) 得到弱收敛 | Remark 15，论文行 900--904 | 等价的形式化推论；Lean 返回显式的最小点和弱极限。 |

## 6. 需要特别注意的非等价点

1. **推论 10 的最小值取得性**：[`cor_2.lean`](/home/liyantao/Paper2Lean/theorem_lib/TheoremLib/Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014/items/cor_2.lean) 要求 `hS : (Argmin Theta).Nonempty`。论文把这一步视为 proper/lsc/强凸框架下的标准事实，当前 Lean 代码尚未形式化该存在性证明。
2. **命题 12 的连续性接口**：[`prop_6.lean`](/home/liyantao/Paper2Lean/theorem_lib/TheoremLib/Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014/items/prop_6.lean) 增加全局 `Continuous gradPsi`；在论文的 Hypothesis H 中它由 Lipschitz 性给出，但该文件独立于 `hH`，所以接口前提更强。
3. **引理 13 的 `epsilon` 有界性**：[`lem_3.lean`](/home/liyantao/Paper2Lean/theorem_lib/TheoremLib/Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014/items/lem_3.lean) 增加 `IsBoundedUnder`。论文陈述没有这一项。
4. **应用算法的结构假设**：`algo_3`--`algo_8` 多数只编码迭代等式。论文应用还假设集合非空闭凸、权重正且归一化、算子线性连续/非零、以及步长范围；这些没有统一进入 Lean 谓词，因此不能把这些谓词单独当作论文完整算法定理的前提。
5. **索引约定**：`velocity`、`zeta`、`mechanicalEnergy` 和 `auxiliaryG` 使用 `1<=k` 或 `2<=k` 的显式 witness；论文默认正索引。Lean 的 `k+1/k+2` 重索引不改变渐近结论。
6. **扩展实数表示**：论文写 `R union {+infinity}`，Lean 用 `EReal=ℝ∪{+infinity,-infinity}`，并通过 properness、有限值和 `toReal`/coercion 条件排除不允许的 `-infinity` 情形。这是表示层差异，不是主结论差异。

## 总体判定

若比较“论文在 Hypothesis H 及应用章节的完整数学语境”与 Lean 的已证明主结果，主定理链在语义上是对应的；需要把推论 10、命题 12、引理 13 的附加前提明确记录为形式化接口差异。若比较“应用算法谓词自身”，`algo_3`--`algo_8` 是论文迭代公式的宽化版本，不能声称包含了论文所有结构/收敛假设。除上述点外，没有发现公式编号错配或核心结论方向相反的情况。

## 7. 逐条上下文与公式编号索引

下面的索引把每个 Lean 文件放回论文叙述中。公式编号是论文中的编号；“无独立编号”表示该 Lean 文件是定义、标准工具或证明辅助命题，论文没有给它单独编号。

### 7.1 定义与主算法

| Lean 条目 | 文章上下文位置 | 公式/编号 |
|---|---|---|
| `def_1.lean` `IFBHypothesis` | 第 2 节 “Standing hypotheses”，先介绍 `Phi` 的 proper/lsc/convex、`Psi` 的可微和 Lipschitz 梯度，再给出步长范围和 `Theta=Phi+Psi` 的凸性/下界。 | Hypothesis `H`：`H_Phi`、`H_Psi`、`H_lambda`、`H_Theta`；无单独公式（论文行 122--132）。 |
| `algo_1.lean` `IsIFBTrajectory` | 引言末段给出离散 IFB：每步先算 `u_{k+1}`，再算 `y_{k+1}`。 | `(IFB)`，公式行 90--92；近端改写为 `(2.1)`。 |
| `def_2.lean` `gamma` / `gamma_pos` | 第 3.1 节“Energy decrease”，定义机械能前的参数。 | `(3.1)`；`gamma_pos` 对应“由 `H_lambda` 可知 `gamma>0`”。 |
| `def_3.lean` `velocity` | 第 3.1 节定义系统速度差分，随后用于机械能和平方可和结论。 | `xi_k=u_k-u_{k-1}`，服务于 `(3.2)`；无单独公式标签（论文行 159--169）。 |
| `def_4.lean` `mechanicalEnergy` | 第 3.1 节在定义 `xi_k` 后引入机械能，并证明其下降。 | `(3.2)`。 |
| `def_5.lean` `zeta` | 第 3.1 节为推导 (3.6)--(3.10) 引入 `y` 的差分。 | `(3.3)`。 |
| `def_6.lean` `zSequence` / `HasZSubgradient` | 第 3.1 节由 IFB 第一更新构造 `z_k`，并记录其属于 `-partial Phi(u_k)`。 | `(3.4)`。 |
| `def_7.lean` `auxiliaryG` | 第 3.2 节“Liapunov-type sequence”，先定义 `G_k(q)`，再定义 `F_k(q)`。 | `(3.11)`；其增量在 `(3.15)` 和后续等式中使用。 |
| `def_8.lean` `liapunovF` | 第 3.2 节紧接 `G_k(q)` 定义 Liapunov 序列，并给出 `alpha`、`delta`。 | `(3.12)`。 |
| `def_9.lean` `auxiliaryA` | 第 3.4 节证明定理 1 时，将 `F_k(q)` 的前两项单独记为 `A_k(q)`。 | `(3.23)`。 |
| `def_10.lean` `IsBoundedlyInfCompact` | 第 4.1.3 节定义 bounded inf-compact 函数及其带范数约束的下水平集。 | `Gamma_r^R` 的集合定义，论文行 608--612；无公式标签。 |

### 7.2 能量、Liapunov 和主收敛链

| Lean 条目 | 文章上下文位置 | 公式/编号 |
|---|---|---|
| `prop_1.lean` `proposition2_beta_pos` | 第 3.1 节最后，用步长条件保证能量差分估计中的耗散系数严格为正。 | `(3.10)` 中 `beta=(2(a+b)-b lambda L_Psi)/(2b lambda)>0`。 |
| `prop_1.lean` `proposition2` | 第 3.1 节主命题：先由次梯度不等式和 descent lemma 得 `(3.5)`、`(3.6)`，相加得到 `(3.7)`，再结合 `(3.8)`、`(3.9)` 和 `(3.10)`。 | PROPOSITION 2；结论为 `E_k` 非增、`xi` 平方可和、`Theta(u_k)` 与 `E_k` 同极限（论文行 183--186）。 |
| `prop_2.lean` `proposition3` | 第 3.2 节说明 `F_k(q)` 与目标函数的关系：先由凸性得到支持不等式，再证明差分恒等式。 | PROPOSITION 3；核心为 `(3.13)`，向量关系为 `(3.14)`，代数展开为 `(3.15)`--`(3.17)`。 |
| `prop_3.lean` `proposition4` | 第 3.2 节在 `G_k(q)` 的展开式中分别估计端点次梯度项、速度项和 `z_i-z_{i-1}` 项。 | PROPOSITION 4；证明使用 `(3.18)`--`(3.21)`，最终给出 `G_k(q)` 上界。 |
| `lem_1.lean` `lemma5` | 第 3.3 节先给出一个实序列递推引理，用于从 `F_k` 的增量和距离平方的非负性推出目标极限不低于任意 `Theta(q)`。 | LEMMA 5；递推式未编号，应用位置为论文行 418--432。 |
| `prop_4.lean` `proposition6` | 第 3.3 节“Minimization, boundedness, and stability”，利用 `(3.22)` 和 Lemma 5 证明算法是最小化序列，并处理无最小点时的范数逃逸。 | PROPOSITION 6；关键估计为 `(3.22)`。 |
| `lem_2.lean` `lemma7` | Proposition 8 之前的辅助递推结果，用于控制 `||u_k-q||`。 | LEMMA 7；递推式未编号，论文行 460--468。 |
| `prop_5.lean` `proposition8` | 第 3.3 节在 `q in S` 时应用 Proposition 3 的单调性和 `(3.22)`，得到迭代序列有界以及 `F_k(q)` 收敛。 | PROPOSITION 8；无额外公式标签，直接依赖 `(3.22)`。 |
| `thm_1.lean` `theorem1` | 第 3.4 节“Proof of Theorem 1”，分单点、`Phi` 可微、`gradPsi` 弱到弱连续、`Psi` 凸四种情形证明唯一弱聚点。 | THEOREM 1；定理陈述在论文行 140--149；证明还使用 `(3.23)`--`(3.26)` 和 Opial 引理。 |

### 7.3 强收敛、`y_k` 和序列引理

| Lean 条目 | 文章上下文位置 | 公式/编号 |
|---|---|---|
| `cor_1.lean` `ifb_lipschitz_constant_pos` | 第 2 节步长讨论中，正步长和严格上界隐含 `L_Psi>0`；Lean 将这个隐含事实单列。 | 无独立公式；服务于 Hypothesis `H_lambda` 和有限维推论。 |
| `cor_1.lean` `corollary9` | 第 4.1.1 节有限维情形：弱收敛在有限维空间等同于强收敛。 | COROLLARY 9；无单独公式，依据 THEOREM 1。 |
| `cor_2.lean` `corollary10` | 第 4.1.2 节强凸性：先给出强凸版本的支持不等式，再得 `F` 的强下降，最后得到唯一最小点处的强收敛。 | `(4.1)`；COROLLARY 10。 |
| `cor_3.lean` `corollary11` | 第 4.1.3 节 bounded inf-compactness：弱收敛时序列有界且落在相对紧的下水平集内，从而强收敛。 | `Gamma_r^R` 定义及 COROLLARY 11；无公式标签。 |
| `prop_6.lean` `proposition12` | 第 4.2 节从 IFB 第二更新出发，定义 `w_k`，把递推改写为收缩形式，再分别证明弱/强收敛。 | `(4.2)` 为第二更新，`(4.3)` 为极限关系，`(4.4)` 定义 `w_k`，`(4.5)` 为收缩递推；PROPOSITION 12。 |
| `lem_3.lean` `eventually_lt_of_contract_recurrence` | Proposition 12 证明中用于处理带常数误差的收缩递推。 | 无独立编号；对应论文 Lemma 13 证明中的几何级数估计（论文行 649--667）。 |
| `lem_3.lean` `limsup_le_zero_of_eventually_lt_pos` | 将“对每个正数最终小于该正数”转换成 `limsup<=0` 的实数序列工具。 | 无独立编号；是 Lean 对 Lemma 13 证明的中间分解。 |
| `lem_3.lean` `lemma13` | 第 4.2 节在 Proposition 12 之前陈述的一般收缩递推引理。 | LEMMA 13；递推式 `p_{k+1}<=eta p_k+epsilon_k` 未单独编号。 |
| `rem_1.lean` `remark15` | 第 5.2 节 Pareto front 讨论末尾，说明当 `Psi` 凸时可直接使用定理 1 的条件 (iv)。 | Remark 15；无公式标签，论文行 900--904。 |

### 7.4 第 5 节应用算法

| Lean 条目 | 文章上下文位置 | 公式/编号 |
|---|---|---|
| `ext_def_1.lean` | 论文在引言、定理 1 和命题 6 中使用 `S=Argmin(Theta)`，但不重新定义集合。 | `S=Argmin(Theta)` 出现在 THEOREM 1、PROPOSITION 6；无独立公式。 |
| `ext_def_2.lean` | IFB 第一更新、`z_k` 定义和凸支持不等式都使用 `partial Phi`。 | `(IFB)`、`(3.4)`、`(3.14)`。 |
| `ext_def_3.lean` | THEOREM 1 的条件 (ii)/(iii) 分别讨论 `grad Phi` 或 `grad Psi` 的弱到弱序列连续性。 | THEOREM 1 条件 (ii)、(iii)；无公式标签。 |
| `ext_def_4.lean` | 第 4.1.2 节把普通凸支持不等式加强为带 `rho/2*||u_k-q||^2` 的强凸不等式。 | `(4.1)`；COROLLARY 10。 |
| `ext_def_5.lean` | 第 2 节先定义 proximity operator，再把 IFB 写成近端形式；第 5.3 节用同一概念表示 ISTA/IFB 的软阈值步。 | 近端定义为论文行 108--117；算法 `(2.1)`；软阈值 `(5.16)`--`(5.17)`。 |
| `ext_def_6.lean` | 第 5.1 节将 `Phi=delta_C` 时的 proximity operator 识别为 `Proj_C`，后续梯度投影和 CQ 都使用该投影。 | `(5.1)`、`(5.4)`、`(5.6)`、`(5.13)`、`(5.14)`。 |
| `ext_def_7.lean` | 第 5.1 节明确取 `Phi=delta_C`，把硬约束写成指标函数。 | `Phi=delta_C` 的文字设定；用于 `(5.1)`。 |
| `ext_def_8.lean` | 第 5.1.1 节定义 `dist(v,C_i)^2` 惩罚，第 5.1.2 节改用 `dist(Av,Q)^2` 的 split-feasibility 惩罚。 | `(5.2)`、`(5.3)`、`(5.9)`；梯度为 `(5.10)`。 |
| `ext_thm_1.lean` | 第 3.4 节最后用 Opial 引理把“所有弱聚点属于 S + 距离极限存在”升级为整列弱收敛。 | Opial 引理无论文公式编号；应用于 THEOREM 1 的证明。 |
| `ext_thm_2.lean` | 第 3.1 节对 `Psi` 使用 Lipschitz 梯度的 descent lemma，得到能量估计。 | `(3.6)`；原始不等式见论文行 207--223。 |
| `algo_2.lean` `IsGradientProjectionTrajectory` | 第 5.1 节 `Phi=delta_C` 且 `a=b=1`，先投影得到 `u_{k+1}`，再作 `y` 的梯度更新。 | `(5.1)`。 |
| `algo_3.lean` `IsClassicalGradientProjectionTrajectory` | 第 5.1.1 节硬约束可行性问题的经典 forward-backward/gradient-projection 算法。 | `(5.4)`；目标问题为 `(5.2)`，惩罚函数为 `(5.3)`。 |
| `algo_4.lean` `IsGeneralIFBGradientProjection` | 第 5.1.1 节在 `a=b=1` 和 `a=b` 特例后给出一般正参数的 IFB 梯度投影。 | `(5.6)`；特定参数展开式为 `(5.7)`。 |
| `algo_5.lean` `IsCQTrajectory` | 第 5.1.2 节 split feasibility：经典 forward-backward 应用于 `delta_C(v)+1/2 dist(Av,Q)^2`。 | CQ 更新 `(5.13)`；问题 `(5.8)`、惩罚 `(5.9)`、梯度 `(5.10)`、Lipschitz 界 `(5.11)`、最小化问题 `(5.12)`。 |
| `algo_6.lean` `IsIFBCQTrajectory` | 第 5.1.2 节把 IFB 应用于同一 CQ 结构化最小化问题。 | `(5.14)`；步长范围在论文行 864--870。 |
| `algo_7.lean` `IsISTATrajectory` | 第 5.3 节信号恢复：先给出 RLS 和 `l^1` 正则化问题，再介绍软阈值近端和 ISTA。 | RLS 无编号，`l^1` 问题 `(5.15)`，软阈值 `(5.16)`--`(5.17)`，ISTA `(5.18)`。 |
| `algo_8.lean` `IsIFBSignalRecoveryTrajectory` | 第 5.3 节将 IFB 应用于 `(5.15)`，得到带近端步和惯性辅助序列 `y_k` 的信号恢复算法。 | `(5.19)`；步长和 `L_Psi=2 rho(A^t A)` 的说明在论文行 950--956。 |

