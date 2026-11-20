-- audit2: 7d0968dad3e8672a6213dc0e508983c17f14eaaa inputs sha256 b3e2631992a041109ef8ab3a4836cc24453830556fb4a9c55f9a166f68e2cde1
-- audit2 baselines: 23cbebdfe9d75717f3f248bb0069ebd9dc9bbef6, cddf4d2dac6a409e64204686cf743e703350a6f6
import Verso
import VersoManual
import VersoBlueprint
import Mathlib.AlgebraicTopology.Quasicategory.InnerFibration
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.AllEdges
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.BaseChange
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianCancellation
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianEdge
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianFibration
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianOpposite
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianCancellation
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianEdge
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.Composition
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.Coslice
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CosliceConverse
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CrossingComparison
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.FiberwiseEssentialSurjectivity
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.FunctorIso
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.InvertibleCartesian
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.Isofibration
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.LeftFibrationFiberComparison
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.LeftFibrationFiberReflection
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.LocalSectionComparison
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.PullbackCartesianFibration
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.PullbackCartesianPair
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.RelativeFunctorInverse
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.RelativeFunctorPostEquivalence
import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SectionsFiberwiseEquivalence
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsofibrationCriterion
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.SliceTrivialFibration
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.TrivialFibrationCocone

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "5.1 Cartesian Fibrations" =>
%%%
number := false
tag := "kerodon-5-1"
%%%

Kerodon の 5.1 節（[Tag 01T1](https://kerodon.net/tag/01T1)）の項目と、SerrePositivity・Mathlib の宣言との対応。本文は対応表（research/kerodon-coverage）の判定の理由の要約で、Kerodon の本文の写しではない。

# 5.1.1 Cartesian Edges of Simplicial Sets

%%%
number := false
tag := "kerodon-5-1-1"
%%%

Kerodon [Tag 01T4](https://kerodon.net/tag/01T4)

*cocartesian-definition.html — 2. ∞ 圏の定義（HTT Def. 2.4.2.1、Kerodon Def. 5.1.4.1） — 外側のホーン $`\Lambda^n_0` を使う理由*

- \*\*$`n=2`（存在）\*\*：$`\Lambda^2_0` は辺 $`0\to1`（$`=f`）と $`0\to2`（$`=g\colon x\to z`）からなり、底では 2 単体全体が与えられている。持ち上げは辺 $`1\to2`（$`=h\colon y\to z`）と $`h\circ f\simeq g` を示す 2 単体を与える。1 圏の条件の存在の部分そのもの。

- \*\*$`n\ge3`（一意性）\*\*：1 圏の一意性は、∞ 圏では「$`h` を選ぶ空間が可縮」になる。可縮性は全ての次元の球面が埋まることなので、全ての $`n` の持ち上げとして書かれる。

:::definition "kerodon_5_1_1_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.HasCocartesianHornLifting")
Kerodon Definition 5.1.1.1（[Tag 01T5](https://kerodon.net/tag/01T5)）。対応表の状態：本体にある。

*主張*　単体集合の射 $`q:X\to S` に関し、辺 $`e` が $`q`-デカルトであるとは、$`n\geq2` の右外角の最後の辺を $`e` とした任意の相対持ち上げ問題に解があることをいう。$`q`-余デカルトでは、左外角の最初の辺を $`e` とする。

仮定：任意の単体集合の射 q:X→S と X の 1 単体 e（Kerodon と一致）。結論：cartesian は終辺 e を固定した最後の外ホーンの持ち上げ性、cocartesian は初辺 e を固定した最初の外ホーンの持ち上げ性（一致）。

*03-straightening.html — 1. cocartesian 辺と cocartesian fibration — 定義*

$`p\colon X\to B` の辺 $`e` が \*\*$`p`-cocartesian\*\* とは、最初の辺が $`e` であるような外側ホーン $`\Lambda^{n+2}_0\to X` の、$`p` に関する持ち上げ問題がすべて解けることをいう（Kerodon Def. 5.1.1.1）。

\`\`\`text
def IsCocartesianEdge \{X B : SSet.\{u\}\} (p : X ⟶ B) (e : X \_⦋1⦌) : Prop :=
  ∀ (n : ℕ) (a : (horn (n + 2) 0 : SSet.\{u\}) ⟶ X)
    (b : (Δ\[n + 2\] : SSet.\{u\}) ⟶ B),
    a.app (Opposite.op ⦋1⦌) (initialHornEdge n) = e →
    ∀ sq : CommSq a (horn (n + 2) 0).ι p b, sq.HasLift
\`\`\`

*cocartesian-definition.html — 2. ∞ 圏の定義（HTT Def. 2.4.2.1、Kerodon Def. 5.1.4.1）*

2. *cocartesian 辺*：辺 $`f\colon x\to y` が $`p`-cocartesian とは、全ての $`n\ge2` について、$`\Delta^{\{0,1\}}` が $`f` に写る $`\Lambda^n_0\to E` と、両立する $`\Delta^n\to B` からなる持ち上げ問題が必ず解けること（HTT Rem. 2.4.1.4、Kerodon Def. 5.1.1.1）。

:::

:::proposition "kerodon_5_1_1_4" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.hasCocartesianHornLifting_iff_isInvertibleEdge_of_map, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isInvertibleEdge_iff_isCartesianEdge")
Kerodon Example 5.1.1.4（[Tag 01T8](https://kerodon.net/tag/01T8)）。対応表の状態：本体にある。

*主張*　無限圏 $`C` の射が同型であることは、$`C\to\Delta^0` に関してデカルトであること、または余デカルトであることのいずれとも同値である。

仮定：∞ 圏 X から点への射と辺 e（Lean が弱い：像が可逆な一般の内ファイブレーションにも適用）。結論：e の可逆性、cartesian 性、cocartesian 性が同値。点への像は恒等辺（一致）。

:::

:::proposition "kerodon_5_1_1_9" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isInvertibleEdge_iff_isCartesianEdge, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isInvertibleEdge_iff_isCocartesianEdge, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCartesianEdge_of_isInvertibleEdge")
Kerodon Proposition 5.1.1.9（[Tag 01TB](https://kerodon.net/tag/01TB)）。対応表の状態：本体にある。

*主張*　無限圏の内部ファイブレーション $`q:C\to D` で、$`C` の射が同型であることは、その像が同型でかつ射自身が $`q`-デカルトであることと同値である。$`q`-余デカルトを用いても同じ同値が成り立つ。

仮定：∞ 圏間の内ファイブレーション p と始域の辺 e（Kerodon と一致）。結論：e の可逆性は cartesian 性かつ像の可逆性と同値。cocartesian 側にも同じ同値（一致）。

:::

:::corollary "kerodon_5_1_1_10" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCocartesianEdge_constant, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCartesianEdge_of_isInvertibleEdge")
Kerodon Corollary 5.1.1.10（[Tag 01TC](https://kerodon.net/tag/01TC)）。対応表の状態：本体にある。

*主張*　無限圏の間の内部ファイブレーションに関して、恒等射はデカルトかつ余デカルトである。

仮定：∞ 圏間の内ファイブレーション p と頂点 x（Kerodon と一致）。結論：定値 1 単体 id\_x が cocartesian。id\_x の可逆性から cartesian でもある（一致）。

:::

:::corollary "kerodon_5_1_1_11" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isInvertibleEdge_iff_isCartesianEdge") (uses := "kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_1_4_6_10, kerodon_5_1_1_9")
Kerodon Corollary 5.1.1.11（[Tag 023H](https://kerodon.net/tag/023H)）。対応表の状態：一部。

*主張*　標的が Kan 複体である無限圏の内部ファイブレーションについて、射が同型であること、デカルトであること、余デカルトであることは同値である。

底がKanなので像の全辺は可逆。isInvertibleEdge\_iff\_isCartesianEdgeは原文の(1)⇔(2)を同じ辺について直接与える。(3)との同値は引用した型だけにはない。

:::

:::proposition "kerodon_5_1_1_14" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCocartesianEdge_iff_relativeCosliceMap_trivialKanFibration, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.relativeCosliceMap_trivialKanFibration_of_isCocartesianEdge") (uses := "kerodon_1_1_0_6, kerodon_4_3_6_16")
Kerodon Proposition 5.1.1.14（[Tag 01TF](https://kerodon.net/tag/01TF)）。対応表の状態：一部。

*主張*　単体集合の射 $`q:X\to S` に関し、辺 $`e:x\to y` が $`q`-デカルトであることは、$`X_{/e}\to X_{/y}\times_{S_{/q(y)}}S_{/q(e)}` が自明な Kan ファイブレーションであることと同値である。余デカルト性は $`X_{e/}\to X_{x/}\times_{S_{q(x)/}}S_{q(e)/}` が自明な Kan ファイブレーションであることと同値である。

isCocartesianEdge\_iff\_relativeCosliceMap\_trivialKanFibrationは原文後半の同じ相対coslice比較のiff。cartesian/slice側は別なので含めない。

:::

:::corollary "kerodon_5_1_1_15" (uses := "kerodon_1_1_0_6, kerodon_4_3_7_17, kerodon_5_1_1_14")
Kerodon Corollary 5.1.1.15（[Tag 01TG](https://kerodon.net/tag/01TG)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：一点の coslice と元の辺・双対の slice・普通の fibered categoryを照合。coslice の辺の q′-cartesian 性を元の辺で判定する結果。通常の pullback での保存では coslice の join 制約を扱わない。

:::

:::corollary "kerodon_5_1_1_16" (uses := "kerodon_1_1_0_6, kerodon_5_1_1_14")
Kerodon Corollary 5.1.1.16（[Tag 01TH](https://kerodon.net/tag/01TH)）。対応表の状態：なし。

引用はcocartesian辺eの始点へのcoslice制限であり、原文のcartesian辺eと任意A⊆Bの相対cosliceの終点持ち上げの判定ではない。双対で別の射。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.relativeCosliceRestriction_source_of_isCocartesianEdge`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCocartesianEdge_of_relativeCosliceRestriction_source`

:::

# 5.1.2 Cartesian Morphisms of ∞-Categories

%%%
number := false
tag := "kerodon-5-1-2"
%%%

Kerodon [Tag 01TK](https://kerodon.net/tag/01TK)

*cocartesian-definition.html — 2. ∞ 圏の定義（HTT Def. 2.4.2.1、Kerodon Def. 5.1.4.1） — 写像空間による言い換え*

$`f\colon x\to y` が cocartesian ⇔ 任意の $`z` について次の正方形がホモトピー引き戻し。
$$`\begin{array}{ccc} \mathrm{Map}_E(y,z) & \xrightarrow{\ -\circ f\ } & \mathrm{Map}_E(x,z)\\ \downarrow & & \downarrow\\ \mathrm{Map}_B(py,pz) & \xrightarrow{\ -\circ p(f)\ } & \mathrm{Map}_B(px,pz) \end{array}`
1 圏の「$`h` が一意に存在する」を写像空間で書いた形である。

:::proposition "kerodon_5_1_2_1" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_3_3_7_6, kerodon_3_4_1_13, kerodon_4_3_6_8, kerodon_4_3_6_12, kerodon_4_3_6_14, kerodon_4_4_2_14, kerodon_4_4_3_8, kerodon_4_6_5_7, kerodon_4_6_5_10, kerodon_4_6_8_5, kerodon_5_1_1_14")
Kerodon Proposition 5.1.2.1（[Tag 01TL](https://kerodon.net/tag/01TL)）。対応表の状態：なし。

IsStronglyCartesianは通常圏のHom集合の普遍性。原文の準圏の指定Kan写像空間の四角への比較がなく、同じ射のホモトピーpullback判定を直接与えない。

宣言：`CategoryTheory.Functor.IsStronglyCartesian`

:::

:::corollary "kerodon_5_1_2_2"
Kerodon Corollary 5.1.2.2（[Tag 01TN](https://kerodon.net/tag/01TN)）。対応表の状態：なし。

IsStronglyCartesianの通常圏の定義は、原文の脈体のcartesian辺とのiffの片側ではない。nerve比較をする宣言を欠く。

宣言：`CategoryTheory.Functor.IsStronglyCartesian`

:::

:::corollary "kerodon_5_1_2_3" (uses := "kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_3_4_1_5, kerodon_4_6_8_5, kerodon_4_6_8_15, kerodon_5_1_2_1")
Kerodon Corollary 5.1.2.3（[Tag 01TQ](https://kerodon.net/tag/01TQ)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の Hom の引き戻し・薄い底の場合・写像空間の比較を照合。半順序の nerve 上で、各 X の写像空間に対する合成が hKan で同型となる cartesian 辺の判定。薄い nerve の inner 性と区別した。

:::

:::corollary "kerodon_5_1_2_4" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCocartesianEdge_triangle_longEdge, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCocartesianEdge_triangle_second_of_first_long, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCartesianEdge_triangle_longEdge, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCartesianEdge_triangle_first_of_second_long")
Kerodon Corollary 5.1.2.4（[Tag 01TS](https://kerodon.net/tag/01TS)）。対応表の状態：本体にある。

*主張*　無限圏の内部ファイブレーション $`q` と、連続する辺 $`f,g` と長辺 $`h` をもつ二単体を取る。$`g` が $`q`-デカルトなら $`f,h` のデカルト性は同値で、$`f` が $`q`-余デカルトなら $`g,h` の余デカルト性は同値である。

仮定：∞ 圏間の内ファイブレーション q と 2 単体 (f,g,h)（Lean が弱い：始域の ∞ 圏性を明示しない）。結論：g が cartesian なら f と h の cartesian 性が同値。f が cocartesian なら g と h の cocartesian 性が同値（一致）。

:::

:::corollary "kerodon_5_1_2_5" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCocartesianEdge_iff_of_functorIso, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCocartesianEdge_of_functorIso") (uses := "kerodon_1_4_0_1, kerodon_5_1_1_9, kerodon_5_1_2_4")
Kerodon Corollary 5.1.2.5（[Tag 01TT](https://kerodon.net/tag/01TT)）。対応表の状態：一部。

*主張*　無限圏の内部ファイブレーションに関するデカルト性と余デカルト性は、矢印圏における射の同型で保たれる。

A=Δ¹、eを非退化辺とするとisCocartesianEdge\_iff\_of\_functorIsoは原文後半の同じFun(Δ¹,C)内同型でのcocartesian性のiffを直接与える。cartesian側は含めない。

:::

:::corollary "kerodon_5_1_2_6" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge.comp, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge.comp") (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_3_4_1_11, kerodon_5_1_1_1, kerodon_5_1_2_1")
Kerodon Corollary 5.1.2.6（[Tag 01TU](https://kerodon.net/tag/01TU)）。対応表の状態：一部。

*主張*　単体集合の内部ファイブレーション $`p:C\to D`、$`q:D\to E` と $`C` の辺 $`e` を取る。$`p(e)` が $`q`-デカルトなら $`e` の $`p`-デカルト性と $`qp`-デカルト性は同値であり、余デカルト性についても対応する同値が成り立つ。

IsCartesianEdge.compはp-cartesianかつ像がq-cartesianから合成に対しcartesianというiffの順方向を直接返す。逆方向は引用にない。

:::

# 5.1.3 Locally Cartesian Edges

%%%
number := false
tag := "kerodon-5-1-3"
%%%

Kerodon [Tag 01TW](https://kerodon.net/tag/01TW)

:::definition "kerodon_5_1_3_1"
Kerodon Definition 5.1.3.1（[Tag 01TX](https://kerodon.net/tag/01TX)）。対応表の状態：なし。

Mathlibの弱いIsCartesian/IsCocartesianと、底の辺Δ¹への引き戻し後のcartesian辺を比較する型がない。通常圏の類似の定義だけでは数えない。

宣言：`CategoryTheory.Functor.IsCartesian`、`CategoryTheory.Functor.IsCocartesian`

:::

:::proposition "kerodon_5_1_3_7" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_5_1_2_4")
Kerodon Proposition 5.1.3.7（[Tag 01U4](https://kerodon.net/tag/01U4)）。対応表の状態：なし。

引用は大域的なcartesian辺の三角形の取消し。原文の局所cartesian性との比較がなく、gが大域的という仮定だけから同じ局所iffを直接返さない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCartesianEdge_triangle_first_of_second_long`

:::

:::corollary "kerodon_5_1_3_9" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_5_1_1_1, kerodon_5_1_1_9, kerodon_5_1_2_4")
Kerodon Corollary 5.1.3.9（[Tag 01U6](https://kerodon.net/tag/01U6)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：区間 Δ¹ の持ち上げ・一方が大域的な三角形・ファイバー写像空間を照合。指定した底辺と終点に大域 cartesian な持ち上げがあるとき、局所 cartesian な別の持ち上げも大域的となる結論。通常の持ち上げの一意性だけでは局所性から始められない。

:::

:::definition "kerodon_5_1_3_10" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_4_6_1_16, kerodon_4_6_8_1, kerodon_4_6_8_4")
Kerodon Notation 5.1.3.10（[Tag 01U7](https://kerodon.net/tag/01U7)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：区間 Δ¹ の持ち上げ・一方が大域的な三角形・ファイバー写像空間を照合。底の辺を固定した局所 cartesian の写像空間判定。単一ファイバー上の pinched Hom の同型は合成による比較射を与えない。

:::

:::proposition "kerodon_5_1_3_11" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_5_1_2_3, kerodon_5_1_3_10")
Kerodon Proposition 5.1.3.11（[Tag 01U8](https://kerodon.net/tag/01U8)）。対応表の状態：なし。

引用は区間上のcocartesian辺を保つ二つの図式のcoslice写像間の同値の輸送。原文の一つの局所cartesian辺の合成作用の判定とは別の射。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.coslicePostcompFiberMap_source_equivalence_of_target`

:::

# 5.1.4 Cartesian Fibrations

%%%
number := false
tag := "kerodon-5-1-4"
%%%

Kerodon [Tag 01U9](https://kerodon.net/tag/01U9)

*cocartesian-definition.html — 4. 他のファイブレーションとの比較*

- 種類　／　リフティング性質　／　意味
- 内ファイブレーション　／　内ホーン $`\Lambda^n_i`（$`0\lt i\lt n`）　／　ファイバーが準圏
- cocartesian fibration　／　内ホーン ＋ 最初の辺が cocartesian な $`\Lambda^n_0` ＋ cocartesian 持ち上げの存在　／　ファイバーが ∞ 圏、輸送が関手的
- 左ファイブレーション　／　全ての $`\Lambda^n_i`（$`0\le i\lt n`）　／　全ての辺が cocartesian、ファイバーが ∞ 亜群
- cartesian fibration　／　双対：$`\Lambda^n_n`、最後の辺　／　輸送が反変

左ファイブレーションでは全ての辺が cocartesian なので、どの辺が特別かを区別する必要がなく、印なしのリフティング性質だけで書ける。補章 2 §3 の「左 fibration では cocartesian 射を保つ条件が自動」はこのこと。圏のナーブは 2-余骨格的なので、1 圏では $`\Lambda^n_0` の条件は $`n=2`（存在）と $`n=3`（一意性）で尽きる。∞ 圏では全ての $`n` が要る。

:::definition "kerodon_5_1_4_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianFibration, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianFibrations, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianHornFibration")
Kerodon Definition 5.1.4.1（[Tag 01UA](https://kerodon.net/tag/01UA)）。対応表の状態：本体にある。

*主張*　デカルトファイブレーションは、底の各辺を任意の指定された終点を持つデカルト辺として持ち上げられる内部ファイブレーションである。余デカルトファイブレーションでは始点を指定し、余デカルト辺で持ち上げる。

仮定：任意の単体集合の射 p（Kerodon と一致）。結論：内ファイブレーションで、各底の辺を指定終点から cartesian に、または指定始点から cocartesian に持ち上げられる（一致）。

*03-straightening.html — 1. cocartesian 辺と cocartesian fibration — 定義*

$`p` が *cocartesian fibration* とは、inner fibration であって、底の任意の辺に対し、始点を指定した cocartesian な持ち上げが存在することをいう（Kerodon Def. 5.1.4.1）。Lean では \`cocartesianFibrations\`（\`MorphismProperty\`）とそれを包む型クラス \`CocartesianFibration\` の二段で持つ。cartesian 側も同じ形で並んでいる（F1/CartesianFibration）。

第 1 章の Joyal の定理は、「$`B=\Delta^0` のとき、cocartesian 辺は可逆な辺に一致する」という特殊な場合だと読める。実際、証明の道具も同じで、外側ホーンを join で書き直す議論が相対版に一般化されている（Core/Cocartesian\*、Core/RelativeOuterHorn）。

*cocartesian-definition.html — 2. ∞ 圏の定義（HTT Def. 2.4.2.1、Kerodon Def. 5.1.4.1）*

$`p\colon E\to B` を準圏の間の写像とする。

1. *内ファイブレーション*：内ホーン $`\Lambda^n_i\subset\Delta^n`（$`0\lt i\lt n`）に関する右リフティング性質。

3. *cocartesian 持ち上げの存在*：任意の $`x\in E` と $`u\colon p(x)\to b` について、$`u` の上の $`p`-cocartesian 辺 $`x\to y` が存在する。

1〜3 を満たすとき $`p` を cocartesian fibration という。1 はリフティング性質だが、3 は「特定の性質を持つ持ち上げの存在」なので、$`p` 単独のリフティング性質にはなっていない。

:::

:::proposition "kerodon_5_1_4_8" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianFibration_pullback_snd, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianFibration_pullback_snd") (uses := "kerodon_1_1_0_6, kerodon_5_1_1_1, kerodon_5_1_4_1")
Kerodon Proposition 5.1.4.8（[Tag 023J](https://kerodon.net/tag/023J)）。対応表の状態：一部。

*主張*　単体集合の射 $`X\to S` がデカルトファイブレーションであることは、$`S` の全単体に沿う引き戻しがデカルトファイブレーションであることと同値である。

cartesianFibration\_pullback\_sndに各σ:Δⁿ→Sを代入すれば原文の順方向そのもの。全ての単体上から大域性を回収する逆は含まない。

:::

:::proposition "kerodon_5_1_4_9" (uses := "kerodon_1_4_0_1, kerodon_5_1_1_1, kerodon_5_1_1_9, kerodon_5_1_4_1")
Kerodon Proposition 5.1.4.9（[Tag 01UG](https://kerodon.net/tag/01UG)）。対応表の状態：なし。

引用はcocartesian fibrationのequivalence lifting。原文のcartesian fibrationからisofibrationという主張とは向きが異なり、反転でisofibrationを輸送する比較を引用型は与えない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianFibration_kanInvertibleTargetLifting`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianFibration_kanEquivalenceLifting`

:::

:::corollary "kerodon_5_1_4_11" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianFibration_kanEquivalenceLifting, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceLifting_iff_inner_and_invertibleTargetLifting, SSet.quasicategory_of_innerFibration")
Kerodon Corollary 5.1.4.11（[Tag 023K](https://kerodon.net/tag/023K)）。対応表の状態：一部。

*主張*　標的が Kan 複体である単体集合の射では、同型ファイブレーション、デカルトファイブレーション、余デカルトファイブレーションであることが同値である。

底Kanは準圏で、cocartesianFibration\_kanEquivalenceLiftingとisofibrationの二条件のiffにより原文(3)⇒(1)が直接得られる。三条件全体の同値ではない。

:::

:::proposition "kerodon_5_1_4_12" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_5_1_4_1")
Kerodon Proposition 5.1.4.12（[Tag 01UJ](https://kerodon.net/tag/01UJ)）。対応表の状態：なし。

引用はcocartesianなhorn liftingと全空間Eでの可逆性のiff。原文はcartesian辺と退化辺上の厳密fiber内での可逆性であり、fiber包含との比較を欠く。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.hasCocartesianHornLifting_iff_isInvertibleEdge_of_map`

:::

:::proposition "kerodon_5_1_4_13" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCartesianEdge_triangle_longEdge, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCartesianEdge_triangle_first_of_second_long") (uses := "kerodon_1_1_0_6, kerodon_5_1_3_7, kerodon_5_1_4_1")
Kerodon Proposition 5.1.4.13（[Tag 01UK](https://kerodon.net/tag/01UK)）。対応表の状態：一部。

*主張*　デカルトファイブレーション $`q` の始域の二単体で、連続する辺 $`f,g` の後者 $`g` がデカルトなら、$`f` がデカルトであることと長辺がデカルトであることは同値である。

底Sを準圏に強めると現本体のisCartesianEdge\_triangle\_longEdgeとisCartesianEdge\_triangle\_first\_of\_second\_longを同じσとgに適用し、原文のfがcartesian iff hがcartesianを直接得る。一般の単体集合の底ではない。

:::

:::proposition "kerodon_5_1_4_14" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianFibration_comp, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianFibration_comp, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge.comp") (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_5_1_1_1, kerodon_5_1_1_9, kerodon_5_1_4_1, kerodon_5_1_4_12, kerodon_5_1_4_13")
Kerodon Proposition 5.1.4.14（[Tag 01UL](https://kerodon.net/tag/01UL)）。対応表の状態：一部。

*主張*　二つのデカルトファイブレーション $`p,q` の合成 $`qp` はデカルトファイブレーションである。辺 $`e` が $`qp`-デカルトであることは、$`e` が $`p`-デカルトで $`p(e)` が $`q`-デカルトであることと同値である。

cartesianFibration\_compは原文の合成のcartesian fibration性、IsCartesianEdge.compは辺の判定の十分条件を直接与える。辺の必要条件は含まない。

:::

:::proposition "kerodon_5_1_4_15" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.rightFibration_iff_cartesianFibration_all_edges, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.leftFibration_iff_cocartesianFibration_all_edges") (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_1_4_6_10, kerodon_4_4_2_1, kerodon_5_1_1_1, kerodon_5_1_3_9, kerodon_5_1_4_1, kerodon_5_1_4_12")
Kerodon Proposition 5.1.4.15（[Tag 01UM](https://kerodon.net/tag/01UM)）。対応表の状態：一部。

*主張*　単体集合の射が右ファイブレーションであることは、デカルトファイブレーションであってすべての辺がデカルトであることと同値である。全辺の条件を全頂点ファイバーが Kan 複体であることに替えても同値である。

rightFibration\_iff\_cartesianFibration\_all\_edgesは同じqについて原文(1)⇔(2)そのもの。(3)の全fiber Kanとの同値は含まない。

:::

:::corollary "kerodon_5_1_4_16" (uses := "kerodon_1_1_0_6, kerodon_5_1_1_1, kerodon_5_1_4_1, kerodon_5_1_4_13")
Kerodon Corollary 5.1.4.16（[Tag 01UN](https://kerodon.net/tag/01UN)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：相対 slice/coslice・充満な全空間の部分複体・Kan・左右反転を照合。全辺が q-cartesian な単体で張る部分複体が右ファイブレーションとなる主張。通常の quasicategory core は可逆辺で張る。

:::

:::proposition "kerodon_5_1_4_17" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_1_2_15, kerodon_5_1_1_1, kerodon_5_1_4_1, kerodon_5_1_4_12, kerodon_5_1_4_13")
Kerodon Proposition 5.1.4.17（[Tag 02R5](https://kerodon.net/tag/02R5)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：相対 slice/coslice・充満な全空間の部分複体・Kan・左右反転を照合。充満部分複体で cartesian lift の始点を選べる場合の制限と辺の判定。任意の底変換とは全空間の部分複体に沿う点が異なる。

:::

:::proposition "kerodon_5_1_4_18" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp_trivialKanFibration")
Kerodon Proposition 5.1.4.18（[Tag 01UP](https://kerodon.net/tag/01UP)）。対応表の状態：一部。

*主張*　デカルトファイブレーション $`q:X\to S` は任意の図式 $`f:K\to X` に対してデカルトファイブレーション $`X_{/f}\to S_{/qf}` を誘導する。そのデカルト辺は $`X` への射影で $`q`-デカルトになる辺である。

qをtrivial Kan fibrationに強めればsliceOverPostcomp\_trivialKanFibrationは原文(1)の同じslice後合成がtrivial Kan、従ってcartesian fibrationと直接与える。一般のqと(2)は含めない。

:::

:::lemma_ "kerodon_5_1_4_19" (uses := "kerodon_1_1_0_6, kerodon_4_3_6_10, kerodon_5_1_1_15, kerodon_5_1_2_6")
Kerodon Lemma 5.1.4.19（[Tag 01UQ](https://kerodon.net/tag/01UQ)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：相対 slice/coslice・充満な全空間の部分複体・Kan・左右反転を照合。coslice の制限比較で、像の辺が q-cartesian なら比較射に対しても cartesian となる主張。単なる coslice 制限の内ファイブレーション性では辺ごとの条件が出ない。

:::

:::proposition "kerodon_5_1_4_20" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.trivialKanFibration_sliceUnderPostcomp") (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_3_6_8, kerodon_5_1_1_1, kerodon_5_1_1_16, kerodon_5_1_4_1, kerodon_5_1_4_12, kerodon_5_1_4_13, kerodon_5_1_4_19")
Kerodon Proposition 5.1.4.20（[Tag 01UR](https://kerodon.net/tag/01UR)）。対応表の状態：一部。

*主張*　デカルトファイブレーション $`q:X\to S` は任意の図式 $`f:K\to X` に対してデカルトファイブレーション $`X_{f/}\to S_{qf/}` を誘導する。そのデカルト辺は $`X` への射影で $`q`-デカルトになる辺である。

qをtrivial Kan fibrationに強めればtrivialKanFibration\_sliceUnderPostcompは原文(1)の同じcoslice後合成がtrivial Kan、従ってcartesian fibrationと直接与える。一般のqと(2)は含めない。

:::

:::proposition "kerodon_5_1_4_21" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianFibration_pullback_over, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCartesianEdge_pullback_over") (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_5_1_1_1, kerodon_5_1_2_6, kerodon_5_1_4_1, kerodon_5_1_4_12, kerodon_5_1_4_13")
Kerodon Proposition 5.1.4.21（[Tag 02VV](https://kerodon.net/tag/02VV)）。対応表の状態：一部。

*主張*　同じ底 $`S` 上にデカルトファイブレーション $`U_i:X_i\to S` と内部ファイブレーション $`U:X\to S` があり、二つの射 $`F_i:X_i\to X` がデカルト辺を保ち、$`F_1` が同型ファイブレーションとする。引き戻し $`X_0\times_X X_1\to S` はデカルトファイブレーションで、そのデカルト辺は両成分がデカルトな辺である。

全空間と底を準圏、F₀をinner fibration、各fiber上のF₀にもinvertible target liftingを追加するとcartesianFibration\_pullback\_overは原文と同じ合成射のcartesian fibration性を直接与える。辺の必要条件と元のF₁だけの仮定への一般化は含まない。

:::

:::corollary "kerodon_5_1_4_22" (uses := "kerodon_1_1_0_6, kerodon_4_3_6_8, kerodon_5_1_1_1, kerodon_5_1_4_1, kerodon_5_1_4_20, kerodon_5_1_4_21")
Kerodon Corollary 5.1.4.22（[Tag 03LL](https://kerodon.net/tag/03LL)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：相対 slice/coslice・充満な全空間の部分複体・Kan・左右反転を照合。cartesian 辺を保つ底上の射と f の coslice を組み合わせた pullback 比較の cartesian 性。pullback.snd の閉性の型では比較射が異なる。

:::

# 5.1.5 Locally Cartesian Fibrations

%%%
number := false
tag := "kerodon-5-1-5"
%%%

Kerodon [Tag 01UW](https://kerodon.net/tag/01UW)

:::definition "kerodon_5_1_5_1"
Kerodon Definition 5.1.5.1（[Tag 01UX](https://kerodon.net/tag/01UX)）。対応表の状態：なし。

IsPreFiberedは通常圏での弱いcartesian持ち上げ。原文の単体集合のinner fibrationとΔ¹に制限した局所cartesian辺の条件への比較がない。

宣言：`CategoryTheory.Functor.IsPreFibered`

:::

:::proposition "kerodon_5_1_5_9"
Kerodon Proposition 5.1.5.9（[Tag 01V5](https://kerodon.net/tag/01V5)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Δ¹・Δ² 上の大域化・ファイバーの小ささ・切断・右左の双対と sliceを照合。局所 cartesian な fibration で、任意の三角形の辺の条件から個々の辺の大域 cartesian 性を判定。合成・取消しの型は最初から大域的な辺を使う。

:::

:::corollary "kerodon_5_1_5_10"
Kerodon Corollary 5.1.5.10（[Tag 01V6](https://kerodon.net/tag/01V6)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Δ¹・Δ² 上の大域化・ファイバーの小ささ・切断・右左の双対と sliceを照合。局所 cartesian fibration の大域化と、局所 cartesian 辺が三角形で合成に閉じることの同値。大域的な合成補題と区別した。

:::

:::corollary "kerodon_5_1_5_11" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianFibration_pullback_snd")
Kerodon Corollary 5.1.5.11（[Tag 01V7](https://kerodon.net/tag/01V7)）。対応表の状態：一部。

*主張*　単体集合の内部ファイブレーション $`X\to S` がデカルトファイブレーションであることは、$`S` の次元 $`\leq2` の全単体に沿う引き戻しがそうであることと同値である。

cartesianFibration\_pullback\_sndはn≤2の全σにも直接適用でき、原文の順方向を与える。低次元だけからの逆判定は含まない。

:::

:::corollary "kerodon_5_1_5_12" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.rightFibration_iff_cartesianFibration_all_edges")
Kerodon Corollary 5.1.5.12（[Tag 046V](https://kerodon.net/tag/046V)）。対応表の状態：一部。

*主張*　局所デカルトファイブレーションについて、右ファイブレーションであること、全頂点ファイバーが Kan 複体であること、全辺が局所デカルトであること、全辺がデカルトであることは同値である。

qを大域cartesian fibrationに強めるとrightFibration\_iff\_cartesianFibration\_all\_edgesは原文(1)⇔(4)を直接返す。locallyの定義と(2),(3)の同値は含まない。

:::

:::proposition "kerodon_5_1_5_13"
Kerodon Proposition 5.1.5.13（[Tag 01V8](https://kerodon.net/tag/01V8)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Δ¹・Δ² 上の大域化・ファイバーの小ささ・切断・右左の双対と sliceを照合。局所 cartesian fibration を図式に沿う slice 比較に移し、局所 cartesian 辺を同定する主張。slice 内ファイブレーションの型だけでは局所性の判定がない。

:::

:::proposition "kerodon_5_1_5_14" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_4_9_8_1, kerodon_4_9_8_7, kerodon_5_1_1_1, kerodon_5_1_2_3, kerodon_5_1_4_1")
Kerodon Proposition 5.1.5.14（[Tag 047P](https://kerodon.net/tag/047P)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Δ¹・Δ² 上の大域化・ファイバーの小ささ・切断・右左の双対と sliceを照合。局所 cartesian fibration の局所 κ-small 性と各頂点ファイバーの局所 κ-small 性の同値。ファイバーの ∞ 圏性に濃度はない。

:::

:::corollary "kerodon_5_1_5_15" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_9_5_5, kerodon_5_1_4_1, kerodon_5_1_5_14")
Kerodon Corollary 5.1.5.15（[Tag 047Q](https://kerodon.net/tag/047Q)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Δ¹・Δ² 上の大域化・ファイバーの小ささ・切断・右左の双対と sliceを照合。局所 cartesian fibration の本質的 κ-small 性を全頂点ファイバーで判定。universe lift の型に任意の非可算 κ はない。

:::

:::corollary "kerodon_5_1_5_16" (uses := "kerodon_1_4_0_1, kerodon_4_9_8_12, kerodon_5_1_5_15")
Kerodon Corollary 5.1.5.16（[Tag 05DV](https://kerodon.net/tag/05DV)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Δ¹・Δ² 上の大域化・ファイバーの小ささ・切断・右左の双対と sliceを照合。非可算正則 κ の下で、局所 cartesian isofibration の全空間と各ファイバーの本質的 κ-small 性を比較。ファイバーごとの同値判定は濃度評価ではない。

:::

:::definition "kerodon_5_1_5_17"
Kerodon Variant 5.1.5.17（[Tag 05DW](https://kerodon.net/tag/05DW)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Δ¹・Δ² 上の大域化・ファイバーの小ささ・切断・右左の双対と sliceを照合。局所 cartesian fibration の n-faithful 性とファイバーの局所 (n−2)-truncation の比較。full faithfulness とファイバーの可縮性だけでは次数一般を扱わない。

:::

:::corollary "kerodon_5_1_5_18"
Kerodon Corollary 5.1.5.18（[Tag 05DX](https://kerodon.net/tag/05DX)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Δ¹・Δ² 上の大域化・ファイバーの小ささ・切断・右左の双対と sliceを照合。右ファイブレーションの n-faithful 性と各ファイバーの (n−1)-truncation の同値。right fibration の Kan ファイバー補題は任意次数を判定しない。

:::

:::proposition "kerodon_5_1_5_19"
Kerodon Proposition 5.1.5.19（[Tag 01V9](https://kerodon.net/tag/01V9)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Δ¹・Δ² 上の大域化・ファイバーの小ささ・切断・右左の双対と sliceを照合。局所 cartesian な二射の四角で、各ファイバーでの局所 cartesian 条件を使う比較。通常の pullback の cartesian 性とは四角の仮定が違う。

:::

# 5.1.6 Fiberwise Equivalence

%%%
number := false
tag := "kerodon-5-1-6"
%%%

Kerodon [Tag 023L](https://kerodon.net/tag/023L)

*route-classification.html — 4. 段 2：左 fibration — 4.5（2.5）fiber ごとの同値の判定*

*定理*：$`B` 上の左 fibration の間の $`B` 上の写像 $`f\colon E\to E'` について、(1) $`\mathrm{LFib}(B)` で同値（$`B` 上の逆写像とホモトピー）、(2) 全ての $`b` で $`f_b\colon E_b\to E'_b` がホモトピー同値、(3)（$`B` 準圏）全空間の圏同値、は同値（(3) は Kerodon Theorem 5.1.6.1 の左 fibration の場合、HTT Prop. 3.3.1.5 も同種）。

*(1)⇒(2)*：$`B` 上の逆写像とホモトピーを fiber に制限する。

*(2)⇒(1)*：$`\mathrm{LFib}(B)` での米田の議論に帰着：全ての左 fibration $`X` で $`f_*\colon\mathrm{Fun}_B(X,E)\to\mathrm{Fun}_B(X,E')` がホモトピー同値なら、$`X=E'` の $`\pi_0` 全射で $`fg\simeq\mathrm{id}`、$`X=E` の $`\pi_0` 単射で $`gf\simeq\mathrm{id}`。$`f_*` がホモトピー同値なことは：

1. *単体一つ*：$`\{0\}\subset\Delta^n` が左アノダインなので $`\mathrm{Fun}_B(\Delta^n,E)\to E_{\sigma(0)}` は自明 Kan fibration、よって $`f_*` は $`f_{\sigma(0)}` と同一視できる。単体の上の切断は始点の fiber だけで決まる、というのが fiber で判定できる理由の核心。

2. *境界*：制限 $`\mathrm{Fun}_B(\Delta^n,E)\to\mathrm{Fun}_B(\partial\Delta^n,E)` は Kan 複体の間の左 fibration。*補題*：Kan 複体の間の左 fibration は Kan fibration（最後の辺は同値なので相対版 Joyal で $`\Lambda^n_n` が持ち上がる）。

3. *セルごとに組み立てる*：骨格に沿って $`\mathrm{Fun}_B(X_k,E)=\mathrm{Fun}_B(X_{k-1},E)\times_{\mathrm{Fun}_B(\partial\Delta^n,E)}\mathrm{Fun}_B(\Delta^n,E)`。Kan fibration に沿った引き戻しはホモトピー引き戻し（貼り合わせ補題、塔の逆極限も同様）なので、次元の帰納法で $`f_*` はホモトピー同値。

4. *同値の意味*：$`hN^{hc}(D)=\pi_0D` なので、$`\mathrm{LFib}(B)` の辺の同値は $`\pi_0` の上での可逆性。

*使われ方*：1.4 の写像空間の模型の比較（fiber ごとに同値）を回収。段 6・7 で「$`\mathrm{Un}(\mathrm{St}(E))\to E` は fiber ごとに同値だから同値」と使う。

*Lean での扱い*：(3)（全空間の圏同値）を経由し、「標準単体上の比較による十分条件」で示す。

- 内容　／　宣言　／　ファイル
- 全ての準圏への前合成が同値　／　\`IsPrecompositionEquivalence\`　／　Core/PrecompositionEquivalence
- fiber ごと ⇒ 全空間　／　\`isPrecompositionEquivalence\_of\_leftFibration\_fibers\`　／　F1/Fibrations/LeftFibrationFiberComparison
- 全空間 ⇒ fiber ごと　／　\`vertexFiberMap\_isQCatEquivalence\_of\_precompositionEquivalence\`　／　F1/Fibrations/LeftFibrationFiberReflection
- 判定法　／　\`leftFibration\_precompositionEquivalence\_iff\_fibers\`、\`leftFibration\_isQCatEquivalence\_iff\_fibers\`　／　同上
- $`\mathrm{LFib}(B)` の同値な辺へ　／　\`leftFibrationInfinityEdge\_isInvertible\_of\_precompositionEquivalence\`　／　F1/Fibrations/LeftFibrationInfinityEquivalence
- 全空間で同値な左 fibration は自明 Kan fibration　／　\`trivialKanFibration\_of\_leftFibration\_of\_isQCatEquivalence\`　／　F1/Fibrations/LeftFibrationTrivialComparison

上の説明は後合成で米田の議論をしたが、形式化は前合成（全空間の圏同値）を経由して最後に $`\mathrm{LFib}(B)` の辺に移す。

:::theorem "kerodon_5_1_6_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isQCatEquivalence_over_interval_of_endpoint_fibers_of_cocartesian_lifts, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isQCatEquivalence_of_leftFibration_fibers, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isEssentiallySurjective_of_vertexFiberMap") (uses := "kerodon_1_4_0_1, kerodon_4_4_5_9, kerodon_4_5_3_31, kerodon_4_8_4_1, kerodon_5_1_1_1, kerodon_5_1_2_5, kerodon_5_1_4_1, kerodon_5_1_6_6, kerodon_5_1_6_7")
Kerodon Theorem 5.1.6.1（[Tag 023M](https://kerodon.net/tag/023M)）。対応表の状態：一部。

*主張*　無限圏の可換正方形で縦の $`U:C\to D` がデカルトファイブレーション、$`U':C'\to D'` が同型ファイブレーションで、底の横写像が同値とする。全体の横写像 $`F:C\to C'` が同値であることは、全ファイバーで同値を誘導し、デカルト射をデカルト射へ送ることと同値である。この場合 $`U'` もデカルトファイブレーションである。

底射を恒等、両縦射をKan fibrationに制限すればleft fibrationでもあり、isQCatEquivalence\_of\_leftFibration\_fibersは同じ全空間射Fの同値をfiberの同値から直接与える。一般cartesian版やiff全体ではない。

:::

:::corollary "kerodon_5_1_6_2" (uses := "kerodon_1_4_0_1, kerodon_4_4_5_8, kerodon_5_1_4_1, kerodon_5_1_6_1")
Kerodon Corollary 5.1.6.2（[Tag 023N](https://kerodon.net/tag/023N)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：同じ底・Δ¹ の特例・圏同値での辺の移送・普通の圏と反転を照合。両縦が isofibration、両横が ∞ 圏同値の四角で cartesian と cocartesian をそれぞれ移す結果。同型な全空間間の辺の保存より広い。

:::

:::corollary "kerodon_5_1_6_3"
Kerodon Corollary 5.1.6.3（[Tag 023P](https://kerodon.net/tag/023P)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：同じ底・Δ¹ の特例・圏同値での辺の移送・普通の圏と反転を照合。isofibration の四角で両横の ∞ 圏同値から右・左ファイブレーション性を保存・反映。反対圏で左右を交換する定理はこの四角を扱わない。

:::

:::corollary "kerodon_5_1_6_4" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.leftFibration_isQCatEquivalence_iff_fibers, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.leftFibration_precompositionEquivalence_iff_fibers") (uses := "kerodon_1_2_5_1, kerodon_1_4_0_1")
Kerodon Corollary 5.1.6.4（[Tag 01VE](https://kerodon.net/tag/01VE)）。対応表の状態：一部。

*主張*　無限圏の二つの右ファイブレーションの間の可換正方形で、底同士の関手が同値なら、全体同士の関手が同値であることと、各ファイバーに Kan 複体のホモトピー同値を誘導することは同値である。

同じ底上のKan fibration間に制限すれば両縦射はleft/right fibration。leftFibration\_isQCatEquivalence\_iff\_fibersは同じFと同じKan fiberの同値のiffを直接返す。rightのみ・底を変える一般の場合は含まない。

:::

:::lemma_ "kerodon_5_1_6_5" (uses := "kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_3_4_1_13, kerodon_5_1_1_1, kerodon_5_1_2_1")
Kerodon Lemma 5.1.6.5（[Tag 023Q](https://kerodon.net/tag/023Q)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：同じ底・Δ¹ の特例・圏同値での辺の移送・普通の圏と反転を照合。内ファイブレーションの四角で、充満忠実性を使い像辺から元の cartesian 性を反映する結果。通常圏の strongly cartesian の型とは入力が異なる。

:::

:::proposition "kerodon_5_1_6_6" (uses := "kerodon_1_4_0_1, kerodon_5_1_2_5, kerodon_5_1_6_2, kerodon_5_1_6_5")
Kerodon Proposition 5.1.6.6（[Tag 023R](https://kerodon.net/tag/023R)）。対応表の状態：なし。

引用は同じpの下でFunctorIsoによってcocartesian辺を移す型。原文の二つのisofibrationと上下の圏同値に沿うcartesian性の移送とは別の図式。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCocartesianEdge_iff_of_functorIso`

:::

:::proposition "kerodon_5_1_6_7" (uses := "kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_3_2_8_1, kerodon_4_6_1_22, kerodon_4_8_3_39, kerodon_5_1_1_1, kerodon_5_1_3_10, kerodon_5_1_3_11, kerodon_5_1_4_1")
Kerodon Proposition 5.1.6.7（[Tag 01VB](https://kerodon.net/tag/01VB)）。対応表の状態：なし。

引用は区間上のcocartesian liftに基づく充満忠実性。原文のcartesian lift・任意の充満忠実な底射・局所cartesian性と同じ条件を直接述べない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isFullyFaithful_over_interval_of_endpoint_fibers_of_cocartesian_lifts`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesian_crossing_mapping_equivalence_of_target`

:::

# 5.1.7 Equivalence of Inner Fibrations

%%%
number := false
tag := "kerodon-5-1-7"
%%%

Kerodon [Tag 0280](https://kerodon.net/tag/0280)

:::definition "kerodon_5_1_7_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.exists_relativeFunctorInverse_of_precompositionEquivalence") (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1")
Kerodon Definition 5.1.7.1（[Tag 0281](https://kerodon.net/tag/0281)）。対応表の状態：一部。

*主張*　同じ底 $`E` の上の内部ファイブレーションの間の射の相対ホモトピー逆は、$`E` 上の逆向きの射で、両合成が $`E` 上の関手圏で恒等射と同型になるものである。そのような逆をもつ射を $`E` 上の同値と呼ぶ。

left fibrationと準圏の底に制限しFが前合成同値なら、exists\_relativeFunctorInverse\_of\_precompositionEquivalenceは底上の逆射と二つの相対Functor空間での同型を直接構成する。原文の相対逆の構成成分で、任意inner fibrationの述語全体は含まない。

:::

:::proposition "kerodon_5_1_7_5" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.exists_relativeFunctorInverse_of_precompositionEquivalence") (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_4_5_5_10, kerodon_4_5_5_11")
Kerodon Proposition 5.1.7.5（[Tag 0285](https://kerodon.net/tag/0285)）。対応表の状態：一部。

*主張*　内部ファイブレーションの $`E` 上の同値は台の単体集合の圏同値である。両対象が $`E` 上の同型ファイブレーションであれば、台の圏同値から $`E` 上の同値も従う。

底を準圏、U,Vをleft fibrationに強め、Fの前合成同値を仮定するとexists\_relativeFunctorInverse\_of\_precompositionEquivalenceが原文(2)の底上の相対逆と相対単位・余単位を直接返す。一般isofibrationへの拡張と(1)は含まない。

:::

:::corollary "kerodon_5_1_7_8" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_5_1_7_5")
Kerodon Corollary 5.1.7.8（[Tag 0287](https://kerodon.net/tag/0287)）。対応表の状態：なし。

引用のiffの右辺は頂点fiberの同値であり、原文の左辺の底上の相対逆の存在ではない。全空間同値とfiber同値の比較だけを原文の相対逆のiffとして数えない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.leftFibration_isQCatEquivalence_iff_fibers`

:::

:::proposition "kerodon_5_1_7_9" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.relativeFunctorPost_isQCatEquivalence_of_precompositionEquivalence, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.relativeFunctorPost_isQCatEquivalence_on_base, SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.simplicialSectionsMap_homotopyEquivalence_of_fibers") (uses := "kerodon_1_1_0_6, kerodon_1_1_4_1, kerodon_1_1_4_12, kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_3_2_8_1, kerodon_4_4_3_7, kerodon_4_4_5_1, kerodon_4_5_3_31, kerodon_4_5_7_23, kerodon_4_8_4_6, kerodon_5_1_7_8")
Kerodon Proposition 5.1.7.9（[Tag 0288](https://kerodon.net/tag/0288)）。対応表の状態：一部。

*主張*　底 $`E` 上の内部ファイブレーションの間の射が $`E` 上の同値であることは、任意の $`B\to E` からの $`E` 上の関手圏に同値を誘導すること、およびその芯にホモトピー同値を誘導することのいずれとも同値である。各単体 $`\Delta^n\to E` に沿う引き戻しの間で同値になることとも同値である。

底準圏・両縦left fibrationに制限すると、原文(4)は特に全頂点fiberの同値を含む。relativeFunctorPost\_isQCatEquivalence\_on\_baseに恒等底射を代入すれば同じ相対Functor後合成の同値(2)を直接返す。全四条件のiffは含まない。

:::

:::corollary "kerodon_5_1_7_10"
Kerodon Corollary 5.1.7.10（[Tag 05J4](https://kerodon.net/tag/05J4)）。対応表の状態：なし。

引用の結論は全空間Fの本質的全射性・圏同値。原文が判定するのは底上の相対逆の存在で、同値から相対逆へ進む比較が引用型にない。証明の部品だけを数えない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isEssentiallySurjective_of_vertexFiberMap_equivalence`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isQCatEquivalence_iff_fullyFaithful_essentiallySurjective`

:::

:::proposition "kerodon_5_1_7_11" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_4_5_3_33, kerodon_5_1_7_1, kerodon_5_1_7_8, kerodon_5_1_7_9")
Kerodon Proposition 5.1.7.11（[Tag 028E](https://kerodon.net/tag/028E)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：left fibration の場合・Δ¹・各ファイバーの場合・相対同値と引き戻しを照合。同型な F,G に沿う isofibration の二つの引き戻しの底 C 上の比較。通常の pullback が変数の厳密な同型を保つ型では、∞ 圏の Fun 内の同型を扱わない。

:::

:::lemma_ "kerodon_5_1_7_13" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_4_4_9, kerodon_4_4_5_8, kerodon_5_1_7_5")
Kerodon Lemma 5.1.7.13（[Tag 0289](https://kerodon.net/tag/0289)）。対応表の状態：なし。

引用の相対逆は二つの合成と恒等の同型のみ。原文(2)が指定するG∘F=idの厳密等式とF上で恒等になる相対同型の正規化を直接与えない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.exists_relativeFunctorInverse_of_precompositionEquivalence`

:::

:::proposition "kerodon_5_1_7_14" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_5_1_4_1, kerodon_5_1_4_8, kerodon_5_1_4_15, kerodon_5_1_6_2, kerodon_5_1_7_8, kerodon_5_1_7_13")
Kerodon Proposition 5.1.7.14（[Tag 028A](https://kerodon.net/tag/028A)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：left fibration の場合・Δ¹・各ファイバーの場合・相対同値と引き戻しを照合。底上で同値な二つの内ファイブレーション間で各種 fibration・covering の性質を比較する結果。op による左右交換はこの相対同値と異なる。

:::

:::proposition "kerodon_5_1_7_15" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_5_1_1_1, kerodon_5_1_4_1, kerodon_5_1_6_1, kerodon_5_1_7_8, kerodon_5_1_7_9")
Kerodon Proposition 5.1.7.15（[Tag 028B](https://kerodon.net/tag/028B)）。対応表の状態：なし。

引用はleft fibrationの全空間同値とfiber同値のiff。原文のcartesian fibrationの相対逆とcartesian辺保存の判定とは、射の型・比較対象が異なる。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.leftFibration_isQCatEquivalence_iff_fibers`

:::

:::corollary "kerodon_5_1_7_16" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_5_1_4_15, kerodon_5_1_7_15")
Kerodon Corollary 5.1.7.16（[Tag 028C](https://kerodon.net/tag/028C)）。対応表の状態：なし。

引用はleft fibrationの前合成同値と相対逆。right fibrationの同じ射への反転と相対Functor空間の比較が型にないため、双対の類似だけでは数えない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.leftFibration_precompositionEquivalence_iff_fibers`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.leftFibration_isQCatEquivalence_iff_fibers`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.exists_relativeFunctorInverse_of_precompositionEquivalence`

:::

