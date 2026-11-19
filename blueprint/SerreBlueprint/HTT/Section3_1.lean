import Verso
import VersoManual
import VersoBlueprint
import SerrePositivity.InfinityCategories.HTT.Section3_1_3.CoreEquivalence
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianEdge
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianFibration
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PostcompositionCoreDetection
import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.WeakWhitehead
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorComposition
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.F1BFibrationsRightAnodyneTensor

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "HTT 3.1 Marked Simplicial Sets" =>
%%%
number := false
tag := "htt-3-1"
%%%

HTT 3.1 の項目のうち、本体か Mathlib に対応があるもの（対応表 `research/htt-coverage` の状態が「なし」でないもの）。本文は日本語で独立に書いた要約と解説で、原典の本文の写しではない。

# 3.1.1 Marked Anodyne Morphisms

%%%
number := false
tag := "htt-3-1-1"
%%%

原典照合の注記　原稿は余 Cartesian 側を説明する。引用の HTT Proposition 3.1.1.6 は原典では Cartesian 側で、印をつけた底の辺を終点を固定して持ち上げる条件を述べる。

*cocartesian-definition.html — 3. marked 単体的集合での純粋なリフティング性質（HTT §3.1）*

$`E^\natural` を $`E` の $`p`-cocartesian 辺に印をつけたもの、$`B^\sharp` を $`B` の全ての辺に印をつけたものとする。

*定理*（HTT Prop. 3.1.1.6）．$`p` が cocartesian fibration ⇔ $`p\colon E^\natural\to B^\sharp` が marked left anodyne 写像に対する右リフティング性質を持つ。

- marked left anodyne の生成元　／　意味
- 内ホーン $`\Lambda^n_i\subset\Delta^n`（印なし）　／　内ファイブレーション
- $`\{0\}\subset(\Delta^1)^\sharp`　／　cocartesian 持ち上げの存在
- $`\Lambda^n_0\subset\Delta^n`（最初の辺に印）　／　印のついた辺は cocartesian
- $`(\Lambda^2_1)^\sharp\cup(\Delta^2)^\flat\subset(\Delta^2)^\sharp`　／　印のついた辺の合成にも印がつく
- $`K^\flat\subset K^\sharp`（$`K` は Kan 複体）　／　同値には印がつく

印を「cocartesian であるという主張」として持ち歩くことで、存在条件もリフティング性質になる。特に $`\{0\}\subset(\Delta^1)^\sharp` に対する持ち上げが「印のついた辺を持ち上げられる」という条件そのもの。

# 3.1.2 Stability Properties of Marked Anodyne Morphisms

%%%
number := false
tag := "htt-3-1-2"
%%%

:::proposition "htt_3_1_2_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.cofinalIhom_map_rightFibration, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.rightFibration_cartesianFibration, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCartesianEdge_of_rightFibration") (uses := "htt_2_4_2_1")
*HTT 命題 3.1.2.1*　指数のカルテジアン性と点ごとの判定（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=169)）。対応表の状態：一部（special）。

*主張*　Cartesian ファイブレーション $`X\to S` と任意の単体的集合 $`K` に対し、$`X^K\to S^K` も Cartesian ファイブレーションで、その Cartesian 辺は $`K` の各頂点で判定される。

KB-W2原文・型再照合：仮定：Cartesian p と任意の K（Lean が強い：p を right fibration に限定）。結論：同じ ihom K による pK が right、従って Cartesian fibration となり一致。この場合は p と pK の全辺が Cartesian なので点ごとの iff も両辺が成立する。一般の Cartesian fibration の指数は含まない。

関手の間の辺を底の辺に沿って持ち上げるとき、まず各評価先で Cartesian であることを見る。結論は、その点ごとの性質が元の関手模型での Cartesian 性をちょうど特徴づけるというもの。

:::

# 3.1.3 The Cartesian Model Structure

%%%
number := false
tag := "htt-3-1-3"
%%%

:::lemma_ "htt_3_1_3_2" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsQCatEquivalence.postcompose, SerrePositivity.InfinityCategories.HTT.Section3_1_3.IsQCatEquivalence.core, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isQCatEquivalence_of_postcomposition_core, SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.isWeakHomotopyEquivalence_iff_isQCatEquivalence")
*HTT 補題 3.1.3.2*　関手圏と Kan core による圏同値の判定（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=172)）。対応表の状態：本体にある。

*主張*　∞ 圏の関手が同値であることは、すべての単体的集合 $`K` について後合成が関手 ∞ 圏の同値になること、または後合成がそれらの core のホモトピー同値になることと同値である。

仮定：準圏 C,D と f、任意の単体集合 K（HTT と一致）。結論：f の同値性、全 Fun(K,f) の同値性、全 core(Fun(K,f)) の弱ホモトピー同値性が同値で一致。逆向きは同じ f の postcomposition core detection、Kan core の弱同値との比較を用いる。

core へ移すと非可逆な自然変換は消える。ただし $`K` をすべて動かすため、可逆な比較だけを用いても元の関手の同値性を検出できる。

:::

