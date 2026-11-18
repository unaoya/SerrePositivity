import Verso
import VersoManual
import VersoBlueprint
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Join.Basic
import Mathlib.CategoryTheory.Limits.Cones
import Mathlib.Topology.Order.UpperLowerSetTopology
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.JoinQuasicategory
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.JoinCells
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.RightConeBoundary
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.ConeAnodyne
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Coslice
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.CosliceEndpointFibration
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.CosliceRestriction
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.EquivalenceLimits
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinAnodyne
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinBoundary
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinLeftBoundaryAnodyne
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinLeftColimits
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinLifting
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinMapInnerFibration
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinRightBoundaryAnodyne
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinRightColimits
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.NerveCone
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.RelativeCoslice
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.RelativeSliceRightFibration
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.RightConeMonoAnodyne
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Slice
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.SliceRestriction
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.TrivialFibrationCocone

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "4.3 The Slice and Join Constructions" =>
%%%
number := false
tag := "kerodon-4-3"
%%%

Kerodon の 4.3 節（[Tag 015M](https://kerodon.net/tag/015M)）の項目と、SerrePositivity・Mathlib の宣言との対応。本文は対応表（research/kerodon-coverage）の判定の理由の要約で、Kerodon の本文の写しではない。

# 4.3.1 Slices of Categories

%%%
number := false
tag := "kerodon-4-3-1"
%%%

Kerodon [Tag 015N](https://kerodon.net/tag/015N)

:::definition "kerodon_4_3_1_1" (lean := "CategoryTheory.Over")
Kerodon Construction 4.3.1.1（[Tag 015P](https://kerodon.net/tag/015P)）。対応表の状態：Mathlib にある。

仮定：通常の圏 T と対象 S（Kerodon と一致）。結論：Over S は S に入る射と、S 上で可換な三角形を射とする slice 圏（一致）。

:::

:::definition "kerodon_4_3_1_4" (lean := "CategoryTheory.Under")
Kerodon Variant 4.3.1.4（[Tag 015S](https://kerodon.net/tag/015S)）。対応表の状態：Mathlib にある。

仮定：通常の圏 T と対象 S（Kerodon と一致）。結論：Under S は S から出る射と、S の下で可換な三角形を射とする coslice 圏（一致）。

:::

:::definition "kerodon_4_3_1_8" (lean := "CategoryTheory.Limits.Cone, CategoryTheory.Limits.Cocone")
Kerodon Construction 4.3.1.8（[Tag 015V](https://kerodon.net/tag/015V)）。対応表の状態：Mathlib にある。

仮定：通常の圏 K,C と F:K→C（Kerodon と一致）。結論：Cone F と Cocone F の対象は定値関手から F または F から定値関手への自然変換で、射は頂点の可換三角形。原文の両側のファイバー積の圏を与える（一致）。

:::

# 4.3.2 Joins of Categories

%%%
number := false
tag := "kerodon-4-3-2"
%%%

Kerodon [Tag 0160](https://kerodon.net/tag/0160)

:::definition "kerodon_4_3_2_1" (lean := "CategoryTheory.Join")
Kerodon Definition 4.3.2.1（[Tag 0161](https://kerodon.net/tag/0161)）。対応表の状態：Mathlib にある。

仮定：通常の圏 C,D（Kerodon と一致）。結論：Join C D の対象は直和。各側の Hom を保持し、左から右は一点、逆は空（一致）。

:::

:::lemma_ "kerodon_4_3_2_9"
Kerodon Lemma 4.3.2.9（[Tag 0169](https://kerodon.net/tag/0169)）。対応表の状態：なし。

Join.inclLeft/inclRight と edge は元の包含と混合辺。原文の slice/coslice への特定の持ち上げとその一意性の結論ではなく、構成の材料。

宣言：`CategoryTheory.Join.inclLeft`、`CategoryTheory.Join.inclRight`、`CategoryTheory.Join.edge`

:::

:::proposition "kerodon_4_3_2_10"
Kerodon Proposition 4.3.2.10（[Tag 016A](https://kerodon.net/tag/016A)）。対応表の状態：なし。

mkFunctor の入力は自然変換で、原文の E\_\{/G\} 値の関手ではない。isoMkFunctor も同型までの復元で、指定のslice関手への全単射を得る比較が要る。

宣言：`CategoryTheory.Join.mkFunctor`、`CategoryTheory.Join.isoMkFunctor`

:::

:::proposition "kerodon_4_3_2_13"
Kerodon Proposition 4.3.2.13（[Tag 016D](https://kerodon.net/tag/016D)）。対応表の状態：なし。

mkFunctor と isoMkFunctor は制限を同型まで復元する。原文の厳密な指定制限を持つ関手と自然変換の全単射へ移す比較と逆写像の法則が型にない。

宣言：`CategoryTheory.Join.mkFunctor`、`CategoryTheory.Join.isoMkFunctor`

:::

:::corollary "kerodon_4_3_2_16"
Kerodon Corollary 4.3.2.16（[Tag 016G](https://kerodon.net/tag/016G)）。対応表の状態：なし。

mkFunctor の入力は自然変換で、原文の E\_\{F/\} 値の関手ではない。cosliceとの比較と指定制限の一致がさらに要る。

宣言：`CategoryTheory.Join.mkFunctor`、`CategoryTheory.Join.isoMkFunctor`

:::

:::corollary "kerodon_4_3_2_17"
Kerodon Corollary 4.3.2.17（[Tag 016H](https://kerodon.net/tag/016H)）。対応表の状態：なし。

mkFunctor と isoMkFunctor は対象ごとの延長の部品。指定のCat上のjoinとslice/cosliceの随伴のいずれの構造も直接与えない。

宣言：`CategoryTheory.Join.mkFunctor`、`CategoryTheory.Join.isoMkFunctor`

:::

# 4.3.3 Joins of Simplicial Sets

%%%
number := false
tag := "kerodon-4-3-3"
%%%

Kerodon [Tag 016K](https://kerodon.net/tag/016K)

*定義 4.1 （有限全順序集合での値 $`X^+`）*

有限な全順序集合 $`I`（空でもよい）について、$`I` が空でなければ $`|I|=n+1` として唯一の順序同型 $`r_I\colon I\xrightarrow{\cong}[n]` をとる。単体的集合 $`X` について

$$`X^+(I)=\begin{cases}X([n])&(I\ne\varnothing)\\ \{\ast\}&(I=\varnothing)\end{cases}`

とおく。順序を保つ写像 $`\alpha\colon I\to J` について、$`I\ne\varnothing` なら $`X^+(\alpha)=X(r_J\circ\alpha\circ r_I^{-1})\colon X^+(J)\to X^+(I)`、$`I=\varnothing` なら一点集合への唯一の写像とする。

*注意 （段ごとの公式）*

$`[n]` の始切片は $`\varnothing`、$`\{0,\dots,p\}`（$`0\le p<n`）、$`[n]` のいずれかなので、定義 4.3 は段ごとには

$$`(K\star L)([n])=L([n])\ \sqcup\bigsqcup_{p+1+q=n}K([p])\times L([q])\ \sqcup\ K([n])`

となる（Kerodon Remark 4.3.3.19）。$`I=\varnothing` の成分が $`L([n])`、$`I=\{0,\dots,p\}` の成分が $`K([p])\times L([q])`、$`I=[n]` の成分が $`K([n])` である。この表示で $`\theta` の作用を書くと、$`\theta` の像が $`I` と $`[n]\setminus I` のどちらに入るかで場合分けが要る。

:::definition "kerodon_4_3_3_1" (lean := "Topology.IsLowerSet")
Kerodon Notation 4.3.3.1（[Tag 016L](https://kerodon.net/tag/016L)）。対応表の状態：Mathlib にある。

仮定：線形順序の部分集合 I（Lean が弱い：IsLowerSet に必要なのは LE だけ）。結論：j∈I かつ i≤j なら i∈I となる下方閉性（一致）。

*定義 4.2 （始切片）*

全順序集合 $`J` の部分集合 $`I` が始切片であるとは、$`i\in I`、$`j\le i` なら $`j\in I` となることをいい、$`I\sqsubseteq J` と書く（空集合と $`J` 自身も始切片である）。順序を保つ写像 $`\theta\colon J'\to J` と始切片 $`I\sqsubseteq J` について、$`\theta^{-1}(I)\sqsubseteq J'` である。

:::

:::definition "kerodon_4_3_3_2"
Kerodon Construction 4.3.3.2（[Tag 016M](https://kerodon.net/tag/016M)）。対応表の状態：一部。

Join.Simplex は空区間の値が一点である通常単体集合のcanonicalな増大の場合、初期区間の長さと左右の単体の組という原文の次数別データを直接与える。任意のLin上の増大関手とその全作用は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex`

:::

:::definition "kerodon_4_3_3_9"
Kerodon Notation 4.3.3.9（[Tag 016U](https://kerodon.net/tag/016U)）。対応表の状態：なし。

augObj は次数別の値だけで、Linの反対圏からの関手もその充満部分圏も直接構成しない。空次数の値の一致だけは原文の関手圏の構成ではない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj`

:::

:::proposition "kerodon_4_3_3_11"
Kerodon Proposition 4.3.3.11（[Tag 016W](https://kerodon.net/tag/016W)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：反転・左右交換・空・一点の縮約・通常圏版を照合。空順序の値が一点の Linᵒᵖ 上の関手と SSet の圏同値。augObj は次数ごとの増大単体を定めるだけ。

:::

:::definition "kerodon_4_3_3_13"
Kerodon Construction 4.3.3.13（[Tag 016Y](https://kerodon.net/tag/016Y)）。対応表の状態：一部。

join と joinMap はcanonicalな増大の初期区間の分割式で原文のjoinの単体と射を直接構成する。Lin上の関手圏との可換図式を束ねる同型は含まない。

*定義 4.3 （単体的集合の join）*

単体的集合 $`K,L` の join $`K\star L` を

$$`(K\star L)([n])=\bigsqcup_{I\sqsubseteq[n]}K^+(I)\times L^+([n]\setminus I)`

で定める（$`K^+`、$`L^+` は定義 4.1、始切片は定義 4.2）。$`\theta\colon[m]\to[n]` は、$`I` の成分の元 $`(\sigma,\tau)` を、$`I'=\theta^{-1}(I)` の成分の元

$$`\bigl(K^+(\theta|_{I'})(\sigma),\ L^+(\theta|_{[m]\setminus I'})(\tau)\bigr)`

に送る。ここで $`\theta|_{I'}\colon I'\to I`、$`\theta|_{[m]\setminus I'}\colon[m]\setminus I'\to[n]\setminus I` は $`\theta` の制限である。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso`

:::

:::proposition "kerodon_4_3_3_24" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_innerFibration")
Kerodon Proposition 4.3.3.24（[Tag 02QU](https://kerodon.net/tag/02QU)）。対応表の状態：本体にある。

仮定：単体集合の射 f,g がともに InnerFibration（Kerodon と一致）。結論：joinMap f g も InnerFibration（一致）。

:::

:::corollary "kerodon_4_3_3_25" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.join_quasicategory")
Kerodon Corollary 4.3.3.25（[Tag 02QV](https://kerodon.net/tag/02QV)）。対応表の状態：本体にある。

仮定：X,Y がともに Quasicategory（Kerodon と一致）。結論：join X Y が Quasicategory（一致）。

:::

:::definition "kerodon_4_3_3_26" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointJoinStdSimplexIso")
Kerodon Construction 4.3.3.26（[Tag 0177](https://kerodon.net/tag/0177)）。対応表の状態：本体にある。

仮定：任意の単体集合 X（Kerodon と一致）。結論：join の片側を Δ⁰ に取ると、左錐 Δ⁰⋆X と右錐 X⋆Δ⁰（一致）。

:::

# 4.3.4 Joins of Topological Spaces

%%%
number := false
tag := "kerodon-4-3-4"
%%%

Kerodon [Tag 017E](https://kerodon.net/tag/017E)

:::definition "kerodon_4_3_4_1"
Kerodon Construction 4.3.4.1（[Tag 017F](https://kerodon.net/tag/017F)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：位相空間の join・幾何実現・単体集合版・一点・球面・縮約を照合。位相空間の X×\[0,1\]×Y の両端を射影で潰す join。fatJoin の対象と押し出しは SSet。

:::

:::proposition "kerodon_4_3_4_8"
Kerodon Proposition 4.3.4.8（[Tag 017N](https://kerodon.net/tag/017N)）。対応表の状態：なし。

joinStdSimplexIso は単体集合のjoinの同型。原文は位相的joinからの特定関数 H\_\{p,q\} の同相性であり、実現のjoin比較がさらに要る。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso`

:::

:::definition "kerodon_4_3_4_9"
Kerodon Construction 4.3.4.9（[Tag 017P](https://kerodon.net/tag/017P)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：位相空間の join・幾何実現・単体集合版・一点・球面・縮約を照合。\|X⋆Y\| から位相空間の join \|X\|⋆\|Y\| への連続写像。joinCylinderMap は単体集合の射。

:::

:::proposition "kerodon_4_3_4_11"
Kerodon Proposition 4.3.4.11（[Tag 017R](https://kerodon.net/tag/017R)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：位相空間の join・幾何実現・単体集合版・一点・球面・縮約を照合。片方が有限のときの実現と位相的 join の比較の同相性。単体集合内の太い join の比較は別。

:::

:::corollary "kerodon_4_3_4_12"
Kerodon Corollary 4.3.4.12（[Tag 017S](https://kerodon.net/tag/017S)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：位相空間の join・幾何実現・単体集合版・一点・球面・縮約を照合。実現した左右の錐と位相的錐の同相。pointJoinStdSimplexIso は標準単体上の単体的な錐。

:::

:::corollary "kerodon_4_3_4_13"
Kerodon Corollary 4.3.4.13（[Tag 017T](https://kerodon.net/tag/017T)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：位相空間の join・幾何実現・単体集合版・一点・球面・縮約を照合。任意の X,Y に対する実現と位相的 join の比較の全単射。fatJoinComparison は実現を含まない。

:::

# 4.3.5 Slices of Simplicial Sets

%%%
number := false
tag := "kerodon-4-3-5"
%%%

Kerodon [Tag 017V](https://kerodon.net/tag/017V)

*定義 4.6 （恒等頂点）*

単体的集合 $`B` の頂点 $`b\colon\Delta^0\to B` について、合成 $`\Delta^0\star\Delta^0\to\Delta^0\xrightarrow{b}B` は $`\Delta^0` 上で $`b` となるので、コスライス $`B_{b/}` の頂点を定める。これを $`\mathrm{id}_b` と書く。スライス $`B_{/b}` の頂点 $`\mathrm{id}_b` も同様に定める（定義 4.5）。

*注意 （大きさ）*

定義 4.5 は $`X`、$`K` の大きさを問わず、$`X_{/p}([n])` は集合 $`\mathrm{Hom}_{\mathrm{sSet}}(\Delta^n\star K,X)` の部分集合である。$`X` と $`K` が小さければ $`X_{/p}`、$`X_{p/}` も小さい。定義 4.1 では有限全順序集合の全体を一つの圏としては使わず、個々の $`I` と $`\alpha` に対して値を定めているだけである。

:::definition "kerodon_4_3_5_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection")
Kerodon Construction 4.3.5.1（[Tag 017W](https://kerodon.net/tag/017W)）。対応表の状態：本体にある。

仮定：単体集合間の任意の f:K→X（Kerodon と一致）。結論：sliceOver f の n 単体は f を延長する Δⁿ⋆K→X。構造写像は左因子に沿った前合成（一致）。

*定義 4.5 （スライスとコスライス）*

単体的集合 $`X,K` と射 $`p\colon K\to X` について、単体的集合 $`X_{/p}` と $`X_{p/}` を

$$`X_{/p}([n])=\{\sigma\colon\Delta^n\star K\to X\mid\sigma\circ\iota_K=p\},\qquad X_{p/}([n])=\{\sigma\colon K\star\Delta^n\to X\mid\sigma\circ\iota_K=p\}`

で定め、$`\theta\colon[m]\to[n]` はそれぞれ $`\theta_*\star\mathrm{id}_K`、$`\mathrm{id}_K\star\theta_*` の前合成で作用させる（$`\theta_*` は定義 2.2、$`\star` と $`\iota_K` は定義 4.3・定義 4.4）。$`X_{/p}` をスライス、$`X_{p/}` をコスライスという。

:::

:::definition "kerodon_4_3_5_3" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection")
Kerodon Variant 4.3.5.3（[Tag 017Y](https://kerodon.net/tag/017Y)）。対応表の状態：本体にある。

仮定：単体集合間の任意の f:K→X（Kerodon と一致）。結論：sliceUnder f の n 単体は f を延長する K⋆Δⁿ→X。構造写像は右因子に沿った前合成（一致）。

:::

:::definition "kerodon_4_3_5_6" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverVertex, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderVertex")
Kerodon Notation 4.3.5.6（[Tag 0181](https://kerodon.net/tag/0181)）。対応表の状態：本体にある。

仮定：X の零単体 x（Kerodon と一致）。結論：sliceOverVertex x と sliceUnderVertex x は Yoneda で表した Δ⁰→X による slice と coslice（一致）。

:::

:::definition "kerodon_4_3_5_12" (uses := "kerodon_1_1_0_6")
Kerodon Construction 4.3.5.12（[Tag 0188](https://kerodon.net/tag/0188)）。対応表の状態：一部。

sliceOverUncurry と sliceUnderUncurry をそれぞれ恒等射に適用すると、原文のslice/cosliceの評価による収縮写像を直接構成する。指定の各制限の等式の一式までは引用型にない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry`

:::

:::proposition "kerodon_4_3_5_13" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverEquiv, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderEquiv, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverCurry")
Kerodon Proposition 4.3.5.13（[Tag 0189](https://kerodon.net/tag/0189)）。対応表の状態：本体にある。

仮定：任意の f:K→X と単体集合 A（Kerodon と一致）。結論：A→sliceOver f と K 上で f に等しい A⋆K→X の全単射。coslice では K⋆A に入れ替える（一致）。

:::

:::corollary "kerodon_4_3_5_14" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinLeftUnderAdjunction, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinRightUnderAdjunction")
Kerodon Corollary 4.3.5.14（[Tag 018A](https://kerodon.net/tag/018A)）。対応表の状態：本体にある。

仮定：任意の単体集合 K（Kerodon と一致）。結論：Under K に値を取る左右の join 関手の右随伴が、対応する slice または coslice（一致）。

:::

:::corollary "kerodon_4_3_5_17"
Kerodon Corollary 4.3.5.17（[Tag 018C](https://kerodon.net/tag/018C)）。対応表の状態：一部。

nerveOverIso/nerveUnderIso は図式 K が一点で F が一つの対象 c を選ぶ場合の同じslice/cosliceのnerve比較同型。任意Kとそのホモトピー圏を経由する比較は含まない。

宣言：`SerrePositivity.InfinityCategories.HTT.Section1_2_9.nerveOverIso`、`SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveUnderIso`

:::

:::corollary "kerodon_4_3_5_18"
Kerodon Corollary 4.3.5.18（[Tag 018D](https://kerodon.net/tag/018D)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：通常圏の slice・左右と反転・頂点または同値での比較を照合。h(A⋆B) と hA⋆hB の比較。slice の随伴と通常の Join は双方あるが、この h の交換を示さない。

:::

# 4.3.6 Slices of ∞-Categories

%%%
number := false
tag := "kerodon-4-3-6"
%%%

Kerodon [Tag 018E](https://kerodon.net/tag/018E)

:::proposition "kerodon_4_3_6_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceOverProjection_rightFibration, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceUnderProjection_leftFibration, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceOver_quasicategory")
Kerodon Proposition 4.3.6.1（[Tag 018F](https://kerodon.net/tag/018F)）。対応表の状態：本体にある。

仮定：Quasicategory X と任意の f:K→X（Kerodon と一致）。結論：slice の射影は RightFibration、coslice の射影は LeftFibration。したがって両始域は ∞ 圏（一致）。

*定理 4.8 （quasicategory のスライス）*

$`X` を quasicategory（定義 1.8）、$`K` を単体的集合、$`p\colon K\to X` を射とする。このとき $`X_{/p}` と $`X_{p/}` は quasicategory である（Kerodon Proposition 4.3.6.1）。

:::

:::definition "kerodon_4_3_6_3" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnion, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnion_isPushout")
Kerodon Construction 4.3.6.3（[Tag 018H](https://kerodon.net/tag/018H)）。対応表の状態：本体にある。

仮定：A′,B′ の部分複体の包含（任意の単射の像で表現）（Kerodon と一致）。結論：joinUnion の包含が A⋆B′ と A′⋆B の A⋆B 上の押し出しからの単射（一致）。

:::

:::proposition "kerodon_4_3_6_4" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnion_innerAnodyne_of_rightAnodyne, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnion_innerAnodyne_of_leftAnodyne")
Kerodon Proposition 4.3.6.4（[Tag 018J](https://kerodon.net/tag/018J)）。対応表の状態：本体にある。

仮定：部分複体 A⊆A′、B⊆B′ で左の包含が右アノダインまたは右の包含が左アノダイン（Kerodon と一致）。結論：joinUnion の包含が内アノダイン（一致）。

:::

:::proposition "kerodon_4_3_6_5" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinRightBoundaryMap_innerAnodyne_of_leftAnodyne, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinLeftBoundaryMap_innerAnodyne_of_rightAnodyne")
Kerodon Example 4.3.6.5（[Tag 0235](https://kerodon.net/tag/0235)）。対応表の状態：本体にある。

仮定：右アノダインな f または左アノダインな g（Lean が弱い：点に限らず相手の因子 K は任意）。結論：K=Δ⁰ の join の押し出し境界写像が内アノダイン（一致）。

:::

:::corollary "kerodon_4_3_6_6" (uses := "kerodon_1_1_0_6, kerodon_4_3_6_4")
Kerodon Corollary 4.3.6.6（[Tag 02VK](https://kerodon.net/tag/02VK)）。対応表の状態：なし。

joinUnion はA₀⋆BとA⋆B₀の和で、B₀を空にしても左の全頂点Aが残り、原文のA₀⋆Bそのものではない。別の包含の内anodyne性は証明部品。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnion_innerAnodyne_of_rightAnodyne`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnion_innerAnodyne_of_leftAnodyne`

:::

:::proposition "kerodon_4_3_6_8" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.relativeSliceOverMap_rightFibration, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.relativeCosliceMap_leftFibration")
Kerodon Proposition 4.3.6.8（[Tag 01BZ](https://kerodon.net/tag/01BZ)）。対応表の状態：本体にある。

仮定：内ファイブレーション q:X→S、任意の f:K→X と部分複体 K₀（Kerodon と一致）。結論：slice の相対制限比較射が RightFibration、coslice の相対制限比較射が LeftFibration（一致）。

:::

:::corollary "kerodon_4_3_6_9" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEndpointMap_leftFibration, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.relativeSliceOverMap_rightFibration")
Kerodon Corollary 4.3.6.9（[Tag 01C0](https://kerodon.net/tag/01C0)）。対応表の状態：本体にある。

仮定：内ファイブレーション q:X→S と任意の f:K→X（Kerodon と一致）。結論：終域を X×\_S S\_\{qf/\} とする coslice 射が LeftFibration。slice 版は K₀=∅ の相対比較射で RightFibration（一致）。

:::

:::corollary "kerodon_4_3_6_10" (uses := "kerodon_1_1_0_6")
Kerodon Corollary 4.3.6.10（[Tag 01NS](https://kerodon.net/tag/01NS)）。対応表の状態：なし。

relativeCosliceMap/relativeSliceOverMap は相対fiber productへの射。原文の単なる後合成への比較・射影との合成とその性質がさらに要る。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.relativeCosliceMap_leftFibration`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.relativeSliceOverMap_rightFibration`

:::

:::definition "kerodon_4_3_6_11"
Kerodon Variant 4.3.6.11（[Tag 05P4](https://kerodon.net/tag/05P4)）。対応表の状態：一部。

sliceOverPostcomp\_trivialKanFibration\_of\_rightFibration は K=Δ⁰ の同じ後合成射の自明Kan性を直接返し、従ってright fibrationでもある。一般Kと双対側は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.sliceOverPostcomp_trivialKanFibration_of_rightFibration`

:::

:::corollary "kerodon_4_3_6_12" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_3_6_8")
Kerodon Corollary 4.3.6.12（[Tag 018K](https://kerodon.net/tag/018K)）。対応表の状態：一部。

sliceUnderRestrict\_leftFibration は原文のcoslice側の同じ制限射のleft fibration性。Archiveのslice側は根拠に含めない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict_leftFibration`

:::

:::proposition "kerodon_4_3_6_13" (uses := "kerodon_1_1_0_6, kerodon_4_1_3_1, kerodon_4_3_6_3, kerodon_4_3_6_4")
Kerodon Proposition 4.3.6.13（[Tag 01C1](https://kerodon.net/tag/01C1)）。対応表の状態：一部。

relativeCosliceMap\_trivialKanFibration\_of\_rightAnodyne は原文のright anodyne包含でのcoslice側の同じ相対射の自明Kan性を直接返す。slice側は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.relativeCosliceMap_trivialKanFibration_of_rightAnodyne`

:::

:::corollary "kerodon_4_3_6_14" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverRestrict_trivialKanFibration, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict_trivialKanFibration")
Kerodon Corollary 4.3.6.14（[Tag 018L](https://kerodon.net/tag/018L)）。対応表の状態：本体にある。

仮定：Quasicategory X、f:K→X、左または右アノダインな単射 K₀→K（Kerodon と一致）。結論：左アノダインなら slice 制限、右アノダインなら coslice 制限が自明 Kan ファイブレーション（一致）。

:::

:::lemma_ "kerodon_4_3_6_16" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.joinUnion_rightHorn_boundary_innerAnodyne, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.joinUnion_boundary_leftHorn_innerAnodyne, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.Join.horn_boundary_preimage, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.Join.boundary_horn_preimage")
Kerodon Lemma 4.3.6.16（[Tag 018N](https://kerodon.net/tag/018N)）。対応表の状態：本体にある。

仮定：正次元のホーンと非負次元の境界。p,q のどちら側をホーンにするかで正次元の側を替える（Kerodon と一致）。結論：joinStdSimplexIso 下の horn\_boundary\_preimage と boundary\_horn\_preimage は押し出し join の包含を添字 i または p+1+j のホーンに同定する（一致）。

:::

:::corollary "kerodon_4_3_6_17"
Kerodon Corollary 4.3.6.17（[Tag 0236](https://kerodon.net/tag/0236)）。対応表の状態：一部。

準圏を仮定する二つのprojectionのinstanceは原文(1)⇒(2),(3)を直接返す。(2)または(3)から準圏性への逆方向は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceUnderProjection_leftFibration`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceOverProjection_rightFibration`

:::

:::definition "kerodon_4_3_6_18" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryJoinIso, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.boundary_boundary_preimage")
Kerodon Variant 4.3.6.18（[Tag 02BU](https://kerodon.net/tag/02BU)）。対応表の状態：本体にある。

仮定：p,q≥0（Kerodon と一致）。結論：joinStdSimplexIso の下で境界同士の押し出し join が Δ\^\{p+q+1\} の境界に一致（一致）。

:::

# 4.3.7 Slices of Left and Right Fibrations

%%%
number := false
tag := "kerodon-4-3-7"
%%%

Kerodon [Tag 018P](https://kerodon.net/tag/018P)

:::proposition "kerodon_4_3_7_1" (uses := "kerodon_1_1_0_6, kerodon_1_5_4_13, kerodon_1_5_5_14, kerodon_4_3_6_3, kerodon_4_3_6_4, kerodon_4_3_6_16")
Kerodon Proposition 4.3.7.1（[Tag 018Q](https://kerodon.net/tag/018Q)）。対応表の状態：なし。

joinUnion\_pointBoundary\_anodyne はanodyneだけで、原文のleft/right anodyneの結論とは異なる。joinPoint\_monoの二宣言も、点を置く側では原文が要求する反対側のanodyne性を返さず同じ特殊形の結論にならない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnion_pointBoundary_anodyne`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnion_pointBoundary_horn_anodyne`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.ConeAnodyne.joinPoint_mono_leftAnodyne`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinPoint_mono_rightAnodyne`

:::

:::proposition "kerodon_4_3_7_2" (uses := "kerodon_1_1_0_6, kerodon_4_3_7_1")
Kerodon Proposition 4.3.7.2（[Tag 018R](https://kerodon.net/tag/018R)）。対応表の状態：一部。

relativePointSliceUnderMap\_fibration は K=Δ⁰、K₀=∅、qがKan fibrationの場合の原文coslice側と同じ相対射のKan fibration性。一般K・right fibrationだけの仮定は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.relativePointSliceUnderMap_fibration`

:::

:::corollary "kerodon_4_3_7_3"
Kerodon Corollary 4.3.7.3（[Tag 018S](https://kerodon.net/tag/018S)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：単射の制限・左/右の底変換と Kan の特例・片側が一点を照合。左 fibration による slice と右 fibration による coslice の、X×\_S を終域とする Kan fibration。相対比較の右／左 fibration だけでは結論が異なる。

:::

:::corollary "kerodon_4_3_7_4"
Kerodon Corollary 4.3.7.4（[Tag 018T](https://kerodon.net/tag/018T)）。対応表の状態：一部。

cosliceの二端をKanとも仮定すれば sliceUnderRestrict\_leftFibration と leftFibration\_fibration\_of\_kanComplex から同じ制限射のKan fibration性を直接得る。この全空間Kan性の追加仮定とcoslice側だけに限る。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict_leftFibration`、`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.leftFibration_fibration_of_kanComplex`

:::

:::corollary "kerodon_4_3_7_5"
Kerodon Corollary 4.3.7.5（[Tag 018U](https://kerodon.net/tag/018U)）。対応表の状態：一部。

原文のslice/cosliceの全空間もKanと仮定すると、両projectionのleft/right性とKan昇格の型から同じ二つの射影のKan fibration性を直接得る。全空間のKan性を原文の仮定だけから示したとはしない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceOverProjection_rightFibration`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceUnderProjection_leftFibration`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.rightFibration_fibration_of_kanComplex`、`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.leftFibration_fibration_of_kanComplex`

:::

:::proposition "kerodon_4_3_7_6" (uses := "kerodon_1_1_0_6, kerodon_4_3_7_1")
Kerodon Proposition 4.3.7.6（[Tag 018V](https://kerodon.net/tag/018V)）。対応表の状態：一部。

coslice側について、包含をanodyneかつright anodyneに強めれば relativeCosliceMap\_trivialKanFibration\_of\_rightAnodyne が同じ相対射の自明Kan性を直接返す。一般anodyneだけの場合とslice側は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.relativeCosliceMap_trivialKanFibration_of_rightAnodyne`

:::

:::corollary "kerodon_4_3_7_7"
Kerodon Corollary 4.3.7.7（[Tag 018W](https://kerodon.net/tag/018W)）。対応表の状態：一部。

包含に IsPrecompositionEquivalence も仮定すると、二つの restrict\_trivialKanFibration 宣言が原文と同じ制限射の自明Kan性を直接返す。Kan–Quillen anodyneだけからこの追加仮定を得たとはしない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverRestrict_trivialKanFibration_of_precompositionEquivalence`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict_trivialKanFibration_of_precompositionEquivalence`

:::

:::lemma_ "kerodon_4_3_7_8" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.ConeAnodyne.joinPoint_mono_leftAnodyne, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.ConeAnodyne.joinPoint_boundary_leftAnodyne, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinPoint_mono_rightAnodyne")
Kerodon Lemma 4.3.7.8（[Tag 0196](https://kerodon.net/tag/0196)）。対応表の状態：本体にある。

仮定：単体集合の単射 f:A→B（Kerodon と一致）。結論：Δ⁰⋆f が左アノダイン、f⋆Δ⁰ が右アノダイン（一致）。

:::

:::proposition "kerodon_4_3_7_9" (uses := "kerodon_1_1_0_6, kerodon_3_3_7_7, kerodon_4_3_7_1, kerodon_4_3_7_8")
Kerodon Proposition 4.3.7.9（[Tag 0197](https://kerodon.net/tag/0197)）。対応表の状態：一部。

joinPoint\_mono\_leftAnodyne と joinPoint\_mono\_rightAnodyne は原文で可縮とする因子がそれぞれ Δ⁰ の場合の同じ joinMap の結論。一般の弱可縮な因子は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.ConeAnodyne.joinPoint_mono_leftAnodyne`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinPoint_mono_rightAnodyne`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.coneMap_rightAnodyne`

:::

:::proposition "kerodon_4_3_7_12"
Kerodon Proposition 4.3.7.12（[Tag 0199](https://kerodon.net/tag/0199)）。対応表の状態：一部。

sliceUnderPostcomp\_trivialKanFibration は K=Δ⁰ と left fibration q の場合の同じcoslice後合成の自明Kan性。任意の弱可縮K・slice側は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.ConeAnodyne.sliceUnderPostcomp_trivialKanFibration`

:::

:::corollary "kerodon_4_3_7_13" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.ConeAnodyne.sliceUnderPostcomp_trivialKanFibration, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.sliceOverPostcomp_trivialKanFibration_of_rightFibration")
Kerodon Corollary 4.3.7.13（[Tag 02LK](https://kerodon.net/tag/02LK)）。対応表の状態：本体にある。

coslice側は sliceUnderPostcomp\_trivialKanFibration、slice側も現本体の sliceOverPostcomp\_trivialKanFibration\_of\_rightFibration が点図式の同じ後合成射の自明Kan性を直接返す。両側を満たし、定理名の不足だけでpartialにはしない。

:::

:::corollary "kerodon_4_3_7_14"
Kerodon Corollary 4.3.7.14（[Tag 018Y](https://kerodon.net/tag/018Y)）。対応表の状態：なし。

sliceUnder\_isWeaklyContractible は弱可縮性だけで、原文のslice/cosliceのKan性と終射のホモトピー逆の存在を直接返さない。原文の可縮Kanという同じ結論へ比較する議論が要る。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceUnder_isWeaklyContractible`

:::

:::proposition "kerodon_4_3_7_15"
Kerodon Proposition 4.3.7.15（[Tag 018Z](https://kerodon.net/tag/018Z)）。対応表の状態：なし。

原文の K₀=∅ でも値域は X×\_S S\_\{/qf\} 等であり、単なる S\_\{/qf\} ではない。引用の後合成は始点の指定を忘れる別の射で、同じ特殊形の自明Kan性にはならない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.trivialKanFibration_sliceOverPostcomp`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp_trivialKanFibration`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.trivialKanFibration_sliceUnderPostcomp`、`SerrePositivity.KST.SConstruction.sliceUnderPostcomp_of_trivialKanFibration`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.CosliceTrivialFibration.sliceUnderPostcomp_trivialKanFibration`

:::

:::corollary "kerodon_4_3_7_16"
Kerodon Corollary 4.3.7.16（[Tag 0190](https://kerodon.net/tag/0190)）。対応表の状態：なし。

引用は S\_\{/qf\} または S\_\{qf/\} への後合成で、原文は X×\_S S\_\{/qf\} などへの始点を保持する比較。異なる射の類似の性質はpartialに数えない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.trivialKanFibration_sliceOverPostcomp`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.trivialKanFibration_sliceUnderPostcomp`

:::

:::corollary "kerodon_4_3_7_17" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.trivialKanFibration_sliceOverPostcomp, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.trivialKanFibration_sliceUnderPostcomp")
Kerodon Corollary 4.3.7.17（[Tag 01NT](https://kerodon.net/tag/01NT)）。対応表の状態：本体にある。

仮定：自明 Kan ファイブレーション q:X→S と任意の f:K→X（Kerodon と一致）。結論：sliceOverPostcomp f q と sliceUnderPostcomp f q がともに自明 Kan ファイブレーション（一致）。

:::

:::corollary "kerodon_4_3_7_18"
Kerodon Corollary 4.3.7.18（[Tag 0191](https://kerodon.net/tag/0191)）。対応表の状態：一部。

包含に IsPrecompositionEquivalence も仮定すると二つのrestrict宣言から同じ射の自明Kan性を直接得る。可縮Kan値域だけでは任意の包含についてこの追加仮定を解消していない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverRestrict_trivialKanFibration_of_precompositionEquivalence`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict_trivialKanFibration_of_precompositionEquivalence`

:::

:::corollary "kerodon_4_3_7_19"
Kerodon Corollary 4.3.7.19（[Tag 0192](https://kerodon.net/tag/0192)）。対応表の状態：なし。

射影のleft/right fibration性は自明Kan性という結論そのものではない。可縮な底という仮定だけから全空間・全ファイバーの可縮性を得る比較がさらに要る。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceOverProjection_rightFibration`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceUnderProjection_leftFibration`

:::

