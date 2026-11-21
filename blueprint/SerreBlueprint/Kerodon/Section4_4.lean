-- audit2: 7d0968dad3e8672a6213dc0e508983c17f14eaaa inputs sha256 b3e2631992a041109ef8ab3a4836cc24453830556fb4a9c55f9a166f68e2cde1
-- audit2 baselines: 23cbebdfe9d75717f3f248bb0069ebd9dc9bbef6, cddf4d2dac6a409e64204686cf743e703350a6f6
import Verso
import VersoManual
import VersoBlueprint
import Mathlib.AlgebraicTopology.Quasicategory.InnerFibration
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.LeftFibrationEquivalenceLifting
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CoreKan
import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.F1BKanComplexHomotopyClasses
import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.RelativeFunctorSpace
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.PrismFinalBoundary
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalenceIntervalVertexIso
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePath
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsofibrationCriterion
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FunctorEdgePointwise
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.CoreIsofibration
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.CorePullbackIso
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.CorePullbackRestriction
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.CoreRightFibration
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalencePathFinalLifting
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalencePathInternalHom
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalencePathLifting
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.InvertibleEdgeLifting
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.KanEquivalenceLiftingFibration
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.KanFibrationTools
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.LeftFiberKan
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.OppositeInvolution
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.OppositeLifting
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.OuterHornDuality
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.QuasicategoryCore
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.RelativeInternalHomLifting
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.RelativeOuterHorn
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.RelativeOuterHornOp
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.RelativeRestrictionLifting
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.RightFibrationContractible
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.RightFibrationReflection
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.RightFibrationYoneda
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.SlicePostcompEquivalenceLifting
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.VertexFiber
import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromCategoriesToSimplicialSets.KanCharacterization
import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.OuterHornConverse
import SerrePositivity.KST.LocalizingInvariants.CoreInclusionEquivalenceLifting
import SerrePositivity.KST.SConstruction.CoreSimplicial
import SerrePositivity.KST.SConstruction.KanSourceCoreMap

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "4.4 Isomorphisms and Isofibrations" =>
%%%
number := false
tag := "kerodon-4-4"
%%%

Kerodon の 4.4 節（[Tag 01EM](https://kerodon.net/tag/01EM)）の項目と、SerrePositivity・Mathlib の宣言との対応。本文は対応表（research/kerodon-coverage）の判定の理由の要約で、Kerodon の本文の写しではない。

# 4.4.1 Isofibrations of ∞-Categories

%%%
number := false
tag := "kerodon-4-4-1"
%%%

Kerodon [Tag 01ER](https://kerodon.net/tag/01ER)

:::definition "kerodon_4_4_1_1"
Kerodon Definition 4.4.1.1（[Tag 01EN](https://kerodon.net/tag/01EN)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：1圏の同型持ち上げ・辺の向きの反転・nerve と hCを照合。通常の圏で指定した終点への同型の厳密な持ち上げ。InvertibleTargetLifting の対象は単体集合。

:::

:::proposition "kerodon_4_4_1_3"
Kerodon Proposition 4.4.1.3（[Tag 01EQ](https://kerodon.net/tag/01EQ)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：1圏の同型持ち上げ・辺の向きの反転・nerve と hCを照合。通常の圏の isofibration が F.op と同値。EquivalenceLifting.op の対象は SSet。

:::

:::definition "kerodon_4_4_1_4" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceLifting_iff_inner_and_invertibleTargetLifting, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceLifting_of_innerFibration_of_targetLifting") (uses := "kerodon_1_4_0_1, kerodon_4_1_1_1")
Kerodon Definition 4.4.1.4（[Tag 01ES](https://kerodon.net/tag/01ES)）。対応表の状態：本体にある。

*主張*　無限圏の関手 $`F:C\to D` が同型ファイブレーションであるとは、内部ファイブレーションであり、$`F(c)` に入る任意の同型を終点 $`c` の同型に持ち上げられることである。

equivalenceLifting\_iff\_inner\_and\_invertibleTargetLifting の右辺は、原文と同じ inner 性と終点指定の可逆辺の可逆な持ち上げ。原文と同じ準圏間の仮定で EquivalenceLifting が二条件と同値になるので、別名でも定義全体を表す。

:::

:::proposition "kerodon_4_4_1_7"
Kerodon Proposition 4.4.1.7（[Tag 01EU](https://kerodon.net/tag/01EU)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：1圏の同型持ち上げ・辺の向きの反転・nerve と hCを照合。F の isofibration と hF における同型の厳密な持ち上げの iff。既存の持ち上げ条件は辺を直接取る。

:::

:::corollary "kerodon_4_4_1_8" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting.op, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.oppositeFunctor_square, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceLifting_iff_inner_and_invertibleTargetLifting")
Kerodon Corollary 4.4.1.8（[Tag 01EV](https://kerodon.net/tag/01EV)）。対応表の状態：本体にある。

*主張*　無限圏の関手は、反対圏の間の関手が同型ファイブレーションであるとき、かつそのときに限り同型ファイブレーションである。

仮定：∞ 圏間の F（Lean が弱い：EquivalenceLifting.op 自体は任意の単体集合間で成り立つ）。結論：EquivalenceLifting は ∞ 圏上では内ファイブレーションと同値辺持ち上げの組。反転で保たれ、二重反転が恒等なので反対方向にも保たれる（一致）。

:::

:::corollary "kerodon_4_4_1_9"
Kerodon Corollary 4.4.1.9（[Tag 056Z](https://kerodon.net/tag/056Z)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：1圏の同型持ち上げ・辺の向きの反転・nerve と hCを照合。正準写像 C→N(hC) の isofibration 性。h の随伴の単位が存在することだけでは同型の持ち上げは得られない。

:::

:::proposition "kerodon_4_4_1_11" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.leftFibration_liftInvertibleEdge_target, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.leftFibration_invertibleTargetLifting") (uses := "kerodon_1_4_0_1, kerodon_4_4_2_11, kerodon_5_6_7_5")
Kerodon Example 4.4.1.11（[Tag 01EW](https://kerodon.net/tag/01EW)）。対応表の状態：一部。

*主張*　無限圏の間の左ファイブレーションと右ファイブレーションはいずれも同型ファイブレーションである。

leftFibration\_invertibleTargetLifting は原文のleft fibration側の可逆辺を可逆な辺へ持ち上げる条件を直接返す。一般のright側とisofibrationとの同値の一式は引用に含まない。

:::

# 4.4.2 Isomorphisms and Lifting Properties

%%%
number := false
tag := "kerodon-4-4-2"
%%%

Kerodon [Tag 019C](https://kerodon.net/tag/019C)

:::proposition "kerodon_4_4_2_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromCategoriesToSimplicialSets.kanComplex_iff_isGroupoid, SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.kanComplex_ho_isGroupoid, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.kanComplex_of_leftHornFillers") (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_4_4_2_6")
Kerodon Proposition 4.4.2.1（[Tag 019D](https://kerodon.net/tag/019D)）。対応表の状態：一部。

*主張*　単体集合 $`X` が Kan 複体であることは、$`X\to\Delta^0` が Kan、左、または右ファイブレーションであることのいずれとも同値である。同じ条件は $`X` が無限圏ですべての射が同型であること、すなわちホモトピー圏が亜群であることでも表せる。

kanComplex\_iff\_isGroupoid と kanComplex\_of\_leftHornFillers は原文の (b)⇔(c) の準圏上での比較と (e)⇒(b) を直接与える。right fibrationを含む六条件全体は含まない。

:::

:::corollary "kerodon_4_4_2_2"
Kerodon Corollary 4.4.2.2（[Tag 02BV](https://kerodon.net/tag/02BV)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：逆辺または Kan・Δ¹ と可逆区間・通常圏の同型を照合。Duskin nerve の Kan 性と 2-groupoid 性の iff。通常圏の nerve と IsGroupoid の比較は次元が異なる。

:::

:::corollary "kerodon_4_4_2_3" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex_of_leftFibration, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex")
Kerodon Corollary 4.4.2.3（[Tag 019E](https://kerodon.net/tag/019E)）。対応表の状態：本体にある。

*主張*　単体集合の左または右ファイブレーションの任意の頂点上のファイバーは Kan 複体である。

仮定：q:X→S が左または右ファイブレーションで s が S の頂点（Kerodon と一致）。結論：引き戻しで定めた vertexFiber q s が KanComplex（一致）。

:::

:::corollary "kerodon_4_4_2_4" (lean := "SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace_kanComplex")
Kerodon Corollary 4.4.2.4（[Tag 01GY](https://kerodon.net/tag/01GY)）。対応表の状態：一部。

*主張*　単射 $`A\to B` と左または右ファイブレーション $`X\to S` を含む可換正方形の持ち上げの単体集合は Kan 複体である。包含が左ファイブレーションに対して左無害、または右ファイブレーションに対して右無害なら可縮である。

relativeFunctorSpace\_kanComplex は A=∅、qがleft fibrationの場合の同じ底上の写像空間のKan性を直接返す。任意の境界制限とanodyne時の可縮性は含まない。

:::

:::corollary "kerodon_4_4_2_5" (lean := "SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace_kanComplex, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.relativeFunctorSpace_kanComplex_of_rightFibration")
Kerodon Corollary 4.4.2.5（[Tag 01GZ](https://kerodon.net/tag/01GZ)）。対応表の状態：本体にある。

*主張*　左または右ファイブレーション $`X\to S` と任意の単体集合の射 $`B\to S` に対し、$`S` 上の写像の単体集合 $`\operatorname{Fun}_{/S}(B,X)` は Kan 複体である。

仮定：q:X→S が左または右ファイブレーションで g:B→S は任意（Kerodon と一致）。結論：底上の相対関手空間 relativeFunctorSpace q g が KanComplex（一致）。

:::

:::theorem "kerodon_4_4_2_6" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.isInvertibleEdge_iff_hasFinalHornFillers, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.hasFinalHornFillers_of_isInvertibleEdge, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_iff_hasInitialHornFillers")
Kerodon Theorem 4.4.2.6（[Tag 019F](https://kerodon.net/tag/019F)）。対応表の状態：本体にある。

*主張*　無限圏の射 $`u` が同型であることは、$`n\geq2` の左外角 $`\Lambda^n_0` の写像で最初の辺が $`u` であるものすべてが延長できることと同値である。右外角 $`\Lambda^n_n` の最後の辺で同じ条件を課すこととも同値である。

仮定：Quasicategory X と端点を指定した辺 e（Kerodon と一致）。結論：IsInvertibleEdge e と、初辺を固定した最初の外ホーン充填性、終辺を固定した最後の外ホーン充填性はそれぞれ同値（一致）。

*01-quasicategories.html — 3. 可逆な辺と Joyal の定理 — 数学*

辺 $`e\colon x\to y` が*可逆*とは、$`hX` で同型になることをいう。Joyal の定理（HTT Prop. 1.2.4.3、Kerodon Thm. 4.4.2.6）は、これを外側ホーンの充填で特徴づける。

*定理.* quasicategory $`X` の辺 $`e` について次は同値。

1. $`e` は可逆。

2. 最後の辺が $`e` であるような任意の $`\Lambda^{n}_{n}\to X`（$`n\ge 2`）は $`\Delta^n` へ拡張できる。

*01-quasicategories.html — 3. 可逆な辺と Joyal の定理 — 証明の方針（(1) ⇒ (2)）*

鍵は、外側ホーンを join で書き直すことである（\`finalHornJoinIso\`、Core/OuterHornJoin）。

$$`\Lambda^{n+2}_{n+2}\;\cong\;(\partial\Delta^n\star\Delta^1)\;\cup_{\partial\Delta^n\star\Lambda^1_1}\;(\Delta^n\star\Lambda^1_1)\;\subset\;\Delta^n\star\Delta^1\cong\Delta^{n+2}.`

ここで $`\Lambda^1_1=\{1\}` であり、右因子 $`\Delta^1` が問題の最後の辺 $`e` に対応する。join と coslice の随伴（§4）によって、この拡張問題は次の持ち上げ問題に言い換えられる。

$$`\begin{array}{ccc} \{1\} & \longrightarrow & X_{\sigma/}\\ \downarrow & & \downarrow q\\ \Delta^1 & \longrightarrow & X_{\sigma|_{\partial\Delta^n}/} \end{array}`

ここで $`\sigma` は最初の $`n+1` 頂点が張る単体である。§4 の結果から $`q` は左 fibration で、左 fibration は「下の辺が可逆なら、終点を指定して持ち上げられる」（\`leftFibration\_liftHorn\_one\_last\`）。下の辺の可逆性は、その $`X` への像が $`e` であることと、左 fibration $`X_{\sigma|_{\partial\Delta^n}/}\to X` が可逆性を反映すること（\`leftFibration\_reflects\_invertibleEdge\`）から従う。Lean ではこれを \`joinUnion\_extend\_of\_invertible\_rightEdge\` として一般の部分複体 $`K_0\subset K` について示し、$`K=\Delta^n`、$`K_0=\partial\Delta^n` に適用している。

(2) ⇒ (1) では、2 次元のホーンで片側の逆を作り、3 次元のホーンで同じ辺が反対側の逆にもなることを示す。最初の辺の版は反対圏 $`X^{\mathrm{op}}`（\`Core/Opposite\`）を通して双対化している。

*route-classification.html — 3. 段 1：写像空間・同値・関手の ∞ 圏 — 3.2（1.2）同値な辺と Joyal の定理*

*定義*：辺 $`f\colon x\to y` が*同値* ⟺ $`[f]` が $`h\mathcal C` で同型 ⟺ $`g\colon y\to x` と、境界 $`(f,g,\mathrm{id}_x)`、$`(g,f,\mathrm{id}_y)` の 2 単体が存在する。

*定義についての質問：同じ境界の 2 単体が複数あったら、それらをつなぐ中身は要るか*。要らない。境界 $`(f,g,\mathrm{id}_x)` の 2 単体は $`\mathrm{Map}(x,x)` の中の $`gf` から $`\mathrm{id}_x` への道で、$`\pi_1` が非自明なら 3 単体でつなげない別々のものがある（枕の例 2.4 で $`\mathrm{Map}(0,2)\simeq S^1`）。それでも同値は $`f` の*性質*で、$`h\mathcal C` だけで決まり、どの証拠を選んでも結論は同じ。ただし証拠を*データとして*持ち運ぶと話が変わる：

- 証拠の形　／　空間
- 同じ $`g` と二つのホモトピー（quasi-inverse）　／　一般に可縮でない（二つの 2 単体の間を埋めていないため。ホモトピー型理論で qinv が命題でないのと同じ）
- 左逆元と右逆元を別々に持つ　／　可縮
- 同じ $`g` と三角等式の高次セル（随伴同値）　／　可縮
- 自由な同型の圏のナーブ $`J` からの延長　／　可縮（全ての整合性込み）

*定理（Joyal）*：$`\mathcal C` 準圏、$`n\ge2`。$`\sigma_0\colon\Lambda^n_0\to\mathcal C` の最初の辺が同値なら $`\Delta^n` に延びる。双対に $`\Lambda^n_n` で最後の辺が同値なら延びる。最初（最後）の辺が可逆なら外ホーンの延長問題は内ホーンと同様に解ける、という主張。

\*\*$`n=2`（手で）\*\*：$`\Lambda^2_0` は $`f\colon x\to y` と $`h\colon x\to z`。頂点 $`x,y,x,z` の 3 単体を考え、$`d_3=\{0,1,2\}` に左逆の 2 単体 $`(f,f',\mathrm{id}_x)`、$`d_0=\{1,2,3\}` に $`\Lambda^2_1` で作る合成 $`g:=hf'`、$`d_1=\{0,2,3\}` に退化 $`s_0h` を置く。欠けているのは $`d_2` だけなので\*\*内ホーン $`\Lambda^3_2`\*\*。埋めた $`d_2` が $`(f,g,h)`。逆元を一つ挟んで外ホーンを内ホーンに変えた。

\*\*$`n=3`（意味）\*\*：$`\Lambda^3_0` は「$`f` を右から合成した後の関係から $`f` を外す」右キャンセル。全次元まとめると、$`f` を前から合成する操作が選択の空間ごと可逆。

*join・スライス・制限写像*（ここで初めて正式に定義）：

- *join*：$`(K\star L)_n=K_n\sqcup L_n\sqcup\bigsqcup_{i+j+1=n}K_i\times L_j`。$`\Delta^m\star\Delta^n=\Delta^{m+n+1}`、$`\Delta^0\star K` は始点を足した錐（2.3 の $`\Delta^0\star\partial\Delta^n=\Lambda^{n+1}_0`）。ナーブでは圏の join。

- *下のスライス* $`\mathcal C_{p/}`（$`p\colon K\to\mathcal C`）：$`n` 単体は $`K\star\Delta^n\to\mathcal C` で $`K` 上 $`p` のもの。$`\mathrm{Hom}(A,\mathcal C_{p/})=\{K\star A\to\mathcal C,\ K\text{ 上 }p\}`。$`\mathcal C_{x/}` の頂点は射 $`x\to y`、$`\mathcal C_{f/}` の頂点は $`f` を通る分解 $`(g,h,gf\simeq h)`（コンマ圏の ∞ 版）。

- *上のスライス* $`\mathcal C_{/p}`：$`\Delta^n\star K\to\mathcal C` で $`K` 上 $`p` のもの。

- *制限写像*：$`K'\subseteq K` から $`\mathcal C_{p/}\to\mathcal C_{p|_{K'}/}`（$`\mathcal C_{/p}` も同様）。例：$`q\colon\mathcal C_{f/}\to\mathcal C_{x/}` は分解を忘れて $`h` だけ見る、$`\mathcal C_{x/}\to\mathcal C` は終点を取る。

*join とホーンの計算*：$`\Delta^m\star\Delta^n` の面は $`j\le m` で $`(d_j\Delta^m)\star\Delta^n`、$`j\gt m` で $`\Delta^m\star(d_{j-m-1}\Delta^n)`。よって

$$`(\partial\Delta^m\star\Delta^n)\cup(\Delta^m\star\Lambda^n_i)=\Lambda^{m+n+1}_{m+1+i},\qquad(\Lambda^m_i\star\Delta^n)\cup(\Delta^m\star\partial\Delta^n)=\Lambda^{m+n+1}_i .`

前者は $`i\lt n` なら、後者は $`i\gt0` なら内ホーン。弱飽和性で片側を一般の単射に広げ：\*\*任意の単射 $`A\subseteq A'` と $`i\lt n` に対し $`(A\star\Delta^n)\cup(A'\star\Lambda^n_i)\subseteq A'\star\Delta^n` は内アノダイン*（右側も同様）。積の補題（2.6）と違い生成元の計算がホーンそのものになるので直接終わる。帰結：*下のスライスの制限は左 fibration、上のスライスの制限は右 fibration\*\*（$`\mathcal C_{x/}\to\mathcal C` が左 fibration なのは 0.3 の表の正確な形）。

*最初の方針（下のスライス）*：$`\Delta^n=\Delta^{\{0,1\}}\star\Delta^{n-2}` とすると $`\Lambda^n_0=(\Delta^{\{0,1\}}\star\partial\Delta^{n-2})\cup(\{0\}\star\Delta^{n-2})` で、さらに $`(\Delta^1\star\partial\Delta^m)\cup(\{0\}\star\Delta^m)=\Lambda^{m+2}_0`。よって定理は「$`q\colon\mathcal C_{f/}\to\mathcal C_{x/}` が自明 Kan fibration」の言い換えそのもの。$`q` が左 fibration であることは上の計算で $`f` の可逆性なしに出るが、残りの $`\partial\Delta^m` に対する持ち上げを「左 fibration は fiber が可縮なら自明」で示そうとすると、fiber が Kan であること（それ自体 Joyal の定理の帰結）を使って循環する。

*証明（循環しない形、Kerodon Prop. 4.4.2.13 の双対）*：反対側の*上のスライス*を取ると、問題が辺一本の持ち上げになる。

1. *右 fibration は同値を反映する*：$`\theta\colon E\to B` 右 fibration、$`\theta(u)` が同値。底で右逆元の 2 単体 $`(\bar w,\theta u,\mathrm{id})` を取り、$`E` で $`\{1,2\}=u`、$`\{0,2\}=\mathrm{id}_Y` として $`\Lambda^2_2` を持ち上げると $`uv\simeq\mathrm{id}` の $`v`。$`\theta(v)` も同値なので繰り返して $`vw\simeq\mathrm{id}`。$`hE` で $`u=u(vw)=(uv)w=w` なので $`u` は同値。

2. *右 fibration は始点を指定して同値を持ち上げる*：$`\bar v\colon\rho(Y)\to\bar Z` 同値。逆元 $`\bar w` を\*\*終点 $`Y` 指定で\*\*持ち上げ（$`\Lambda^1_1`）$`w\colon Z\to Y`、1 より同値。その逆元 $`w'\colon Y\to Z` について $`[\rho w']=[\bar v]` なので境界 $`(\rho w',\mathrm{id},\bar v)` の 2 単体があり、$`\{0,1\}=w'`、$`\{1,2\}=\mathrm{id}_Z` として内ホーン $`\Lambda^2_1` を持ち上げると $`\{0,2\}` が求める $`v`。

3. *本証明*：$`\Delta^n=\Delta^1\star\Delta^{n-2}`、$`g:=\sigma_0|_{\Delta^{\{2,\dots,n\}}}`、$`g_0:=g|_{\partial\Delta^{n-2}}`。右 fibration $`\mathcal C_{/g}\xrightarrow{\rho}\mathcal C_{/g_0}\xrightarrow{\theta}\mathcal C` を取る。$`Y:=\sigma_0|_{\{0\}\star\Delta^{n-2}}\in\mathcal C_{/g}`、$`\bar v:=\sigma_0|_{\Delta^1\star\partial\Delta^{n-2}}` は $`\mathcal C_{/g_0}` の辺で始点 $`\rho(Y)`、$`\theta(\bar v)=f`。延長 ＝ 始点 $`Y` で $`\bar v` の上の辺（終点が欠けた面 $`d_0`）。1 より $`\bar v` は同値、2 で持ち上がる。∎

$`n=2` では $`\mathcal C_{/g_0}=\mathcal C`、$`\theta=\mathrm{id}` で、手で作った 3 単体の議論と同じ内容。使ったのは join とホーンの計算、内ホーン・$`\Lambda^2_2`・$`\Lambda^1_1` の持ち上げ、ホモトピー圏の計算だけで、fiber が Kan であることも写像空間も使わない。

- 　／　スライス　／　示すべきこと
- 最初の方針　／　$`f` の下 $`\mathcal C_{f/}\to\mathcal C_{x/}`　／　全次元の $`\partial\Delta^m` の持ち上げ
- 証明　／　残りの面の上 $`\mathcal C_{/g}\to\mathcal C_{/g_0}`　／　同値な辺一本の持ち上げ

高次の情報はスライス $`\mathcal C_{/g}` に押し込まれ、問題は 1 次元に落ちる。結果として最初の方針の $`q` も自明 Kan fibration。

*系*：(1) 準圏が Kan 複体 ⟺ $`h\mathcal C` が亜群（⇒ は $`\Lambda^2_0`、$`\Lambda^2_2` で左右の逆元、⇐ は内ホーンと定理）。「∞ 亜群 ＝ Kan 複体」が二つの意味で一致。(2) 予告：同値な辺だけの単体からなる $`\mathcal C^{\simeq}` は準圏でホモトピー圏が亜群、よって Kan 複体（1.3）。(3) $`N(D)` では同値は同型で、定理は自明。

*Lean での扱い*（作業ツリー、HEAD \`d4520692f\`）：Kerodon の向きのまま\*\*最後のホーン $`\Lambda^n_n`・下のスライス・左 fibration\*\*で証明し、$`\Lambda^n_0` は単体的集合の反転で導く（上の説明はそれをもう一度反転した版）。公開の入口は \`Core/InvertibleEdge.lean\`。詳しくは第 1 章。

- 内容　／　宣言　／　ファイル
- 同値（$`h\mathcal C` で同型）　／　\`IsInvertibleEdge\`　／　Core/InvertibleEdgeLifting
- 指定した辺の外ホーン充填条件　／　\`HasInitialHornFillers\`、\`HasFinalHornFillers\`　／　同上
- join とホーンの計算　／　\`rightHornInclusions\`、\`leftHornInclusions\`、\`joinUnion\_rightHorn\_boundary\_innerAnodyne\`、\`joinUnion\_boundary\_leftHorn\_innerAnodyne\`　／　Core/JoinCells
- 一般の単射への拡張とスライスの持ち上げ　／　\`relativeSliceUnderMap\_hasLiftingProperty\`、\`relativeSliceOverMap\_hasLiftingProperty\`、\`joinUnion\_leftHorn\_innerAnodyne\`　／　Core/JoinLifting
- ホーンの join 表示　／　\`finalHornJoinIso\`　／　Core/OuterHornJoin
- 同値の反映　／　\`leftFibration\_reflects\_invertibleEdge\`　／　Core/InvertibleEdgeLifting
- 端点を指定した同値の持ち上げ　／　\`leftFibration\_liftInvertibleEdge\_target\`、\`leftFibration\_liftHorn\_one\_last\`　／　同上
- 本証明　／　\`joinUnion\_extend\_of\_invertible\_rightEdge\`、\`hasFinalHornFillers\_of\_isInvertibleEdge\`　／　同上
- $`\Lambda^n_0` 版　／　\`hasInitialHornFillers\_of\_isInvertibleEdge\`　／　Core/OuterHornDuality
- 逆向き（充填 ⇒ 同値）　／　\`isInvertibleEdge\_of\_hasFinalHornFillers\`、\`isInvertibleEdge\_iff\_hasInitialHornFillers\`　／　Core/OuterHornConverse、OuterHornDuality
- Kan ⟺ 亜群　／　\`kanComplex\_of\_isGroupoid\`、\`kanComplex\_iff\_isGroupoid\`　／　Core/KanCharacterization
- 内 fibration に沿った相対版　／　\`joinUnion\_lift\_of\_invertible\_rightEdge\`　／　Core/RelativeOuterHorn

積 $`\Delta^m\times\Delta^n` をセルごとに埋める版（内ホーンは準圏性、$`\Lambda_0` は Joyal の定理）が \`Core/CellExtension.lean\`、\`Core/PrismExtension.lean\` にあり、1.5 で使う見込み。

:::

:::definition "kerodon_4_4_2_7"
Kerodon Definition 4.4.2.7（[Tag 019G](https://kerodon.net/tag/019G)）。対応表の状態：なし。

isLimitCone\_of\_conservative\_image は原文の保守性を入力仮定に使う別の極限反映の定理。入力仮定の文字列の一致だけは保守性を定義する宣言の対応としない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isLimitCone_of_conservative_image`

:::

:::proposition "kerodon_4_4_2_11" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.leftFibration_reflects_invertibleEdge, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.derived_rightFibration_reflects_invertibleEdge")
Kerodon Proposition 4.4.2.11（[Tag 019K](https://kerodon.net/tag/019K)）。対応表の状態：本体にある。

*主張*　無限圏の間の左または右ファイブレーションは同型を反映する。

仮定：Quasicategory X,Y と左または右ファイブレーション q:X→Y（Kerodon と一致）。結論：任意の辺 e について q(e) が可逆なら e も可逆（一致）。

:::

:::corollary "kerodon_4_4_2_12" (uses := "kerodon_1_4_0_1, kerodon_4_3_6_1, kerodon_4_4_2_11")
Kerodon Corollary 4.4.2.12（[Tag 02BW](https://kerodon.net/tag/02BW)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：逆辺または Kan・Δ¹ と可逆区間・通常圏の同型を照合。F が同型を反映することから左右の slice の後合成も同型を反映する主張。相対制限の fibration 補題は別の条件。

:::

:::proposition "kerodon_4_4_2_13" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.innerFibration_lift_finalHorn, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.innerFibration_lift_initialHorn")
Kerodon Proposition 4.4.2.13（[Tag 01H0](https://kerodon.net/tag/01H0)）。対応表の状態：本体にある。

*主張*　無限圏の間の内部ファイブレーションに対する $`n\geq2` の右外角の持ち上げ問題は、角の最後の辺が始域の同型であれば解をもつ。

仮定：∞ 圏間の内ファイブレーション q、次元≥2 の最後のホーン、可換な底単体と可逆な終辺（Kerodon と一致）。結論：ホーン制限と q による像の双方を保つ充填が存在。引用は最初のホーンの双対版も含む（一致）。

:::

:::proposition "kerodon_4_4_2_14" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.rightFibration_trivialKanFibration_of_contractible_fibers, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_isContractibleKan") (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_4_4_2_15")
Kerodon Proposition 4.4.2.14（[Tag 01NU](https://kerodon.net/tag/01NU)）。対応表の状態：一部。

*主張*　単体集合の射が自明な Kan ファイブレーションであることは、左ファイブレーションで全頂点ファイバーが可縮なこと、または右ファイブレーションで全頂点ファイバーが可縮なことのいずれとも同値である。

rightFibration\_trivialKanFibration\_of\_contractible\_fibers は原文(3)⇒(1)を直接返す。vertexFiber\_isContractibleKanも逆向きの可縮性成分を持つが、left側の全比較は含まない。

:::

:::lemma_ "kerodon_4_4_2_15" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_1_4_6_10, kerodon_3_1_2_12, kerodon_4_2_5_3, kerodon_4_4_2_6")
Kerodon Lemma 4.4.2.15（[Tag 01A7](https://kerodon.net/tag/01A7)）。対応表の状態：なし。

引用はright fibrationと標準単体の最初の頂点の可縮fiber。原文はleft fibrationと最後の頂点を指定しており、opを取る比較をさらに必要とする双対命題そのものはpartialにしない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.rightFibration_fillBoundary_over_stdSimplex`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.rightFibration_liftBoundaryPrism`

:::

# 4.4.3 The Core of an ∞-Category

%%%
number := false
tag := "kerodon-4-4-3"
%%%

Kerodon [Tag 01CZ](https://kerodon.net/tag/01CZ)

*01-quasicategories.html — 3. 可逆な辺と Joyal の定理 — 数学*

最初の辺と $`\Lambda^n_0` についても同様。*系*：quasicategory $`X` が Kan 複体であることと、$`hX` が亜群であることは同値（HTT Prop. 1.2.5.1）。

*route-classification.html — 3. 段 1：写像空間・同値・関手の ∞ 圏 — 3.3（1.3）core $`\mathcal C^{\simeq}`*

*定義*：全ての辺が同値な単体からなる部分単体的集合（面で閉じ、退化辺は恒等なので退化でも閉じる）。

- *準圏*：内ホーンを $`\mathcal C` で埋めると、$`n=2` の新しい辺は同値の合成なので同値、$`n\ge3` では頂点が 4 個以上あるので全ての辺がすでにホーンにある（辺 $`\{a,b\}` は $`j\notin\{a,b,i\}` の面 $`d_j` に含まれる）。外ホーンも $`n\ge3` なら同じ。

- *Kan 複体*：ホモトピーを示す 2 単体 $`(f,\mathrm{id},f')` も逆元とその証拠も $`\mathcal C^{\simeq}` にあるので $`h(\mathcal C^{\simeq})` は $`h\mathcal C` の同型だけの部分亜群、3.2 の系で Kan。直接には、外ホーンも Joyal の定理で $`\mathcal C` で埋めて上の観察で戻す。

- *普遍性*：Kan 複体 $`K` からの写像は必ず $`\mathcal C^{\simeq}` を経由（$`K` の辺は全て同値で、写像は同型を保つ）。$`\mathrm{Hom}(K,\mathcal C^{\simeq})=\mathrm{Hom}(K,\mathcal C)`、つまり core は「Kan 複体 ⊂ 準圏」の右随伴。

- $`\mathcal C`　／　$`\mathcal C^{\simeq}`
- $`N(D)`　／　$`N(D^{\simeq})`
- Kan 複体 $`X`　／　$`X`
- $`\mathrm{Fun}(K,\mathcal C)`　／　全ての関手と自然同値（各点判定は 1.5）
- $`\mathcal S`、$`\mathrm{Cat}_\infty`　／　対象と同値だけ

*注意*：$`\mathrm{Fun}(K,\mathcal C)^{\simeq}`（全ての関手と自然同値）と $`\mathrm{Fun}(K,\mathcal C^{\simeq})`（射を全て同値に送る図式）は違う。定理 I に出るのは前者。

*定理 I での役割*：弱い形は空間の同値（分類空間型）で、$`\mathrm{Map}(B,\mathcal S):=\mathrm{Fun}(B,\mathcal S)^{\simeq}`。$`\mathrm{Cat}_\infty=N^{hc}(\mathrm{QCat}^\Delta)` の豊穣は $`\mathrm{Fun}(X,Y)^{\simeq}` で、Kan であること（$`N^{hc}` が準圏になる条件、補章 3）と、core が積を保つこと（合成を作るため）を使う。

*Lean での扱い*（\`F1/Categories/\`）：

- 内容　／　宣言　／　ファイル
- 定義（全ての辺への制限が \`IsInvertibleEdge\`）　／　\`quasicategoryCore\`　／　QuasicategoryCore
- 普遍性・関手性　／　\`quasicategoryCoreLift\`、\`quasicategoryCoreLift\_ι\`、\`quasicategoryCoreMap\`、\`quasicategoryCoreFunctor\`　／　同上
- 埋めた単体が core に入る　／　\`quasicategoryCore\_horn\_filler\_mem\`、\`isInvertibleEdge\_triangle\_missing\`、\`edge\_mem\_horn\_of\_three\_le\`　／　CoreKan、CoreFaces
- Kan 複体　／　\`quasicategoryCore\_kanComplex\`　／　CoreKan
- Kan 複体の core は自分自身　／　\`quasicategoryCoreIsoOfKan\`　／　F1/KanModels/KanEquivalenceLiftingFibration
- 積を保つ　／　\`quasicategoryCoreProduct\`、\`quasicategoryCoreFunctor\_laxMonoidal\`　／　CoreProduct
- core で写像対象を取り替えた単体的圏　／　\`QCat\`、\`qCat\_sHom\_kanComplex\`　／　QCatSimplicial

Kan 性の証明は「内ホーンは準圏性、外ホーンは Joyal の定理で $`\mathcal C` で埋め、core に戻す」という直接の方針。

:::definition "kerodon_4_4_3_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore_mem_edge_iff, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor")
Kerodon Construction 4.4.3.1（[Tag 01D0](https://kerodon.net/tag/01D0)）。対応表の状態：本体にある。

*主張*　無限圏の芯 $`C^{\simeq}` は、すべての辺が $`C` の同型に移る単体からなる単体部分集合である。

仮定：∞ 圏 X（Lean が弱い：構成は任意の SSet に定義）。結論：各辺が可逆な単体の部分複体 quasicategoryCore X（一致）。

:::

:::proposition "kerodon_4_4_3_6" (lean := "SerrePositivity.KST.LocalizingInvariants.coreInclusion_innerFibration, SerrePositivity.KST.LocalizingInvariants.coreInclusion_equivalenceLifting") (uses := "kerodon_1_4_0_1")
Kerodon Proposition 4.4.3.6（[Tag 01D4](https://kerodon.net/tag/01D4)）。対応表の状態：本体にある。

*主張*　無限圏 $`C` の芯 $`C^{\simeq}` は同型で閉じた部分圏であり、包含 $`C^{\simeq}\to C` は同型ファイブレーションである。

coreInclusion\_equivalenceLifting と equivalenceLifting\_iff\_inner\_and\_invertibleTargetLifting により、同じcore包含は原文のisofibrationの二条件をともに満たす。coreInclusion\_innerFibrationも直接あり、名称の差だけでpartialにしない。

:::

:::proposition "kerodon_4_4_3_7" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.coreMap_fibration_of_kanEquivalenceLifting, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.coreMap_rightFibration_of_invertibleTargetLifting")
Kerodon Proposition 4.4.3.7（[Tag 01EZ](https://kerodon.net/tag/01EZ)）。対応表の状態：本体にある。

*主張*　無限圏の同型ファイブレーションは、芯の間に Kan ファイブレーションを誘導する。

仮定：∞ 圏 X,Y と EquivalenceLifting を持つ p:X→Y（Kerodon と一致）。結論：quasicategoryCoreMap p が Kan ファイブレーション（一致）。

:::

:::corollary "kerodon_4_4_3_8" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.rightFibration_fibration_of_kanComplex, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.fibration_leftFibration") (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_4_4_1_11, kerodon_4_4_2_11, kerodon_4_4_3_7")
Kerodon Corollary 4.4.3.8（[Tag 01NV](https://kerodon.net/tag/01NV)）。対応表の状態：一部。

*主張*　標的が Kan 複体である単体集合の射について、Kan ファイブレーション、左ファイブレーション、右ファイブレーション、無限圏の間の同型を反映する同型ファイブレーションであることは同値である。

rightFibration\_fibration\_of\_kanComplex は始域もKanと仮定すると原文(3)⇒(1)を同じqについて直接返す。fibration\_leftFibrationは(1)⇒(2)。始域が任意の場合と保守的isofibrationの条件は含まない。

:::

:::corollary "kerodon_4_4_3_9"
Kerodon Corollary 4.4.3.9（[Tag 0237](https://kerodon.net/tag/0237)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：通常圏と Kan からの因子化・左/右または引き戻し・単体の条件を照合。Kan 複体を底にする左／右被覆の同値。Quiver の被覆はホーンを用いない。

:::

:::corollary "kerodon_4_4_3_10" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.fibration_of_kanEquivalenceLifting_of_kanComplex")
Kerodon Corollary 4.4.3.10（[Tag 01NW](https://kerodon.net/tag/01NW)）。対応表の状態：本体にある。

*主張*　Kan 複体間の同型ファイブレーションは Kan ファイブレーションである。

仮定：KanComplex X,Y と EquivalenceLifting を持つ p:X→Y（Kerodon と一致）。結論：p が Kan ファイブレーション（一致）。

:::

:::corollary "kerodon_4_4_3_11" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.quasicategoryCore_kanComplex")
Kerodon Corollary 4.4.3.11（[Tag 01H1](https://kerodon.net/tag/01H1)）。対応表の状態：本体にある。

*主張*　無限圏の芯は Kan 複体である。

仮定：Quasicategory X（Kerodon と一致）。結論：quasicategoryCore X を単体集合として見たものが KanComplex（一致）。

:::

:::corollary "kerodon_4_4_3_13"
Kerodon Corollary 4.4.3.13（[Tag 04Q5](https://kerodon.net/tag/04Q5)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：通常圏と Kan からの因子化・左/右または引き戻し・単体の条件を照合。replete 部分圏の core が元の core の直和因子になる主張。全部分複体の包含に直和分解を与える型がない。

:::

:::corollary "kerodon_4_4_3_14" (lean := "SerrePositivity.KST.SConstruction.kanSource_edge_isInvertible, SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.isInvertibleEdge_of_hasFinalHornFillers")
Kerodon Corollary 4.4.3.14（[Tag 01D6](https://kerodon.net/tag/01D6)）。対応表の状態：一部。

*主張*　無限圏の射が同型であることは、ある Kan 複体からの関手で辺の像になることと同値である。その Kan 複体を可縮と要求しても同値である。

kanSource\_edge\_isInvertible と IsInvertibleEdge.map により、Kan複体の辺をFで送ったuは可逆で、原文(2)⇒(1)を直接得る。逆にKan/可縮Kanからの表示を構成する方向は含まない。

:::

:::corollary "kerodon_4_4_3_15" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.exists_equivalenceInterval_map_of_vertexIso") (uses := "kerodon_1_2_5_1, kerodon_1_4_0_1")
Kerodon Corollary 4.4.3.15（[Tag 01H3](https://kerodon.net/tag/01H3)）。対応表の状態：一部。

*主張*　無限圏の二対象が同型であることは、ある連結 Kan 複体の二頂点の像として一つの関手で実現されることと同値である。その Kan 複体を可縮と要求しても同値である。

exists\_equivalenceInterval\_map\_of\_vertexIso は、二対象の同型から同じ二頂点を持つ可逆区間からの射を直接与える。可逆区間はcodiscreteな二点亜群のnerveで可縮Kanであり、(1)から存在条件への向き。一般の逆方向は含まない。

:::

:::definition "kerodon_4_4_3_16" (lean := "SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.nonempty_vertexIso_of_piZero_eq")
Kerodon Notation 4.4.3.16（[Tag 01D7](https://kerodon.net/tag/01D7)）。対応表の状態：一部。

*主張*　無限圏 $`C` の芯の連結成分の集合 $`\pi_0(C^{\simeq})` は、$`C` の対象の同型類の集合である。

nonempty\_vertexIso\_of\_piZero\_eq をKan coreに適用し包含で送ると、同じπ₀成分の二対象が元のCで同型になる方向を直接得る。同型類の集合との全単射・逆方向は含まない。

:::

:::proposition "kerodon_4_4_3_17" (lean := "SerrePositivity.KST.SConstruction.kanSourceCoreMap, SerrePositivity.KST.SConstruction.kanSourceCoreMap_inclusion, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreLift")
Kerodon Proposition 4.4.3.17（[Tag 01D8](https://kerodon.net/tag/01D8)）。対応表の状態：本体にある。

*主張*　Kan 複体から無限圏 $`C` への単体写像は、芯 $`C^{\simeq}` を通って一意に分解する。

仮定：Kan 始域 X、∞ 圏 Y（Lean が弱い：Y は任意）。結論：任意の f:X→Y を core へ因子化し、包含との合成は f。包含が単射なので逆対応は一意（一致）。

:::

:::corollary "kerodon_4_4_3_18" (lean := "SerrePositivity.KST.SConstruction.kanSourceCoreMap, SerrePositivity.KST.SConstruction.kanCoreIso") (uses := "kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_4_4_3_11, kerodon_4_4_3_17")
Kerodon Corollary 4.4.3.18（[Tag 01D9](https://kerodon.net/tag/01D9)）。対応表の状態：一部。

*主張*　無限圏の芯は、その中の最大の Kan 複体である。

kanSourceCoreMap と包含との厳密な回収式をKan部分複体Aの包含に適用するとA⊆coreを直接得る。原文の最大性の成分。core自身のKan性はこの引用の結論に含まない。

:::

:::corollary "kerodon_4_4_3_19" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting.innerFibration, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap_isPullback_of_isPullback, SSet.quasicategory_of_innerFibration") (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_4_4_1_4, kerodon_4_4_3_7, kerodon_4_4_3_11, kerodon_4_4_3_18")
Kerodon Corollary 4.4.3.19（[Tag 01H4](https://kerodon.net/tag/01H4)）。対応表の状態：一部。

*主張*　無限圏の同型ファイブレーション $`C\to D` を無限圏 $`D'\to D` に沿って引き戻すと、再び無限圏の間の同型ファイブレーションが得られる。芯に移した正方形は引き戻しかつホモトピー引き戻しである。引き戻し圏の射が同型であることは、$`C,D'` への二つの像が同型であることと同値である。

quasicategoryCoreMap\_isPullback\_of\_isPullback は同じ指定したcore四角形の厳密なpullback性を直接返す。ホモトピーpullback性・同型の反映・q′のisofibration性は含まない。

:::

:::corollary "kerodon_4_4_3_20" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap_isPullback_of_isPullback, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.corePullbackIso")
Kerodon Corollary 4.4.3.20（[Tag 01H6](https://kerodon.net/tag/01H6)）。対応表の状態：本体にある。

*主張*　無限圏の同型ファイブレーション $`C\to D` では、頂点 $`d` 上のファイバーの芯は $`C^{\simeq}\to D^{\simeq}` の $`d` 上のファイバーに同型である。従ってファイバーの $`C` への包含は同型を反映する。

仮定：∞ 圏の isofibration p と底の点（Lean が弱い：p は内ファイブレーション、底変換は任意の ∞ 圏からでよい）。結論：core と当該厳密な引き戻しを交換する同型。点を代入するとファイバーの比較になる（一致）。

:::

:::corollary "kerodon_4_4_3_21" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.sliceOverPostcomp_equivalenceLifting, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.sliceUnderPostcomp_equivalenceLifting")
Kerodon Corollary 4.4.3.21（[Tag 069C](https://kerodon.net/tag/069C)）。対応表の状態：本体にある。

*主張*　無限圏の同型ファイブレーション $`U:C\to D` と任意の図式 $`f` に対し、$`C_{/f}\to D_{/Uf}` は同型ファイブレーションである。

仮定：EquivalenceLifting を持つ p と任意の図式 f:K→X（Kerodon と一致）。結論：sliceOverPostcomp f p も EquivalenceLifting。coslice の双対も含む（一致）。

:::

:::corollary "kerodon_4_4_3_22" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex_of_leftFibration")
Kerodon Corollary 4.4.3.22（[Tag 04HW](https://kerodon.net/tag/04HW)）。対応表の状態：一部。

*主張*　無限圏間で同型を反映する同型ファイブレーションの各対象上のファイバーは Kan 複体である。

qにさらにrightまたはleft fibrationを仮定すると、vertexFiber\_kanComplexの二宣言から同じ指定fiberのKan性を直接得る。保守的isofibrationだけからの導出は含まない。

:::

:::proposition "kerodon_4_4_3_23" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_4_4_3_17")
Kerodon Proposition 4.4.3.23（[Tag 01DA](https://kerodon.net/tag/01DA)）。対応表の状態：なし。

equivalencePathι\_isIso\_of\_kanComplex の始域は可逆辺の部分複体で、原文はKanパラメータからの関手空間のcore比較。Δ¹はKanでもなく、原文の特殊形としてこの型をそのまま使えない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι_isIso_of_kanComplex`

:::

# 4.4.4 Natural Isomorphisms

%%%
number := false
tag := "kerodon-4-4-4"
%%%

Kerodon [Tag 01DF](https://kerodon.net/tag/01DF)

*route-classification.html — 3. 段 1：写像空間・同値・関手の ∞ 圏 — 3.5（1.5）自然同値は各点で判定できる*

*成分の定義*：$`\mathrm{Fun}(K,\mathcal C)` の辺は $`\alpha\colon\Delta^1\times K\to\mathcal C`、頂点 $`k\colon\Delta^0\to K` での成分は $`\Delta^1\times\{k\}` への制限 $`\alpha_k:=\alpha\circ(\mathrm{id}\times k)\colon\Delta^1\to\mathcal C`、両端は $`F(k)=\alpha|_{\{0\}\times\{k\}}`、$`G(k)=\alpha|_{\{1\}\times\{k\}}`。関手として言えば制限 $`\mathrm{ev}_k\colon\mathrm{Fun}(K,\mathcal C)\to\mathcal C` で $`\alpha_k=\mathrm{ev}_k(\alpha)`。単体 $`\Delta^m\to K` で制限すれば自然性の角柱。

- 条件　／　中身
- $`\alpha` が $`\mathrm{Fun}(K,\mathcal C)` で同値　／　逆向きの辺 $`\beta\colon\Delta^1\times K\to\mathcal C` と、境界 $`(\alpha,\beta,\mathrm{id}_F)`、$`(\beta,\alpha,\mathrm{id}_G)` の 2 単体 $`\Delta^2\times K\to\mathcal C`（$`K` 全体の形をした図式で間を埋める）。$`\mathrm{id}_F` は射影 $`\Delta^1\times K\to K` と $`F` の合成
- 各成分 $`\alpha_k` が $`\mathcal C` で同値　／　頂点ごとにばらばらな逆元と 2 単体 $`\Delta^2\to\mathcal C`

:::definition "kerodon_4_4_4_1"
Kerodon Definition 4.4.4.1（[Tag 01DG](https://kerodon.net/tag/01DG)）。対応表の状態：なし。

FunctorIsoは関手空間のホモトピー圏の同型データ。原文の実際の可逆な自然変換の辺を与える型ではなく、代表を選んで比較する宣言がさらに必要。

宣言：`SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso`、`SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex`

:::

:::theorem "kerodon_4_4_4_4" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.isInvertibleEdge_iff_evaluateFunctorAt, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_iff_evaluateFunctorAt_any, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.functorIsoOfPointwiseInvertibleHomotopy")
Kerodon Theorem 4.4.4.4（[Tag 01DK](https://kerodon.net/tag/01DK)）。対応表の状態：本体にある。

*主張*　無限圏 $`C` の単体図式間の自然変換は、添字単体集合のすべての頂点での成分が $`C` の同型であるとき、かつそのときに限り自然同型である。

仮定：Quasicategory X、図式 f,g:K→X と関手空間の辺 e（Kerodon と一致）。結論：辺の可逆性と、任意の K の頂点で評価した辺の可逆性が同値（一致）。

*route-classification.html — 3. 段 1：写像空間・同値・関手の ∞ 圏 — 3.5（1.5）自然同値は各点で判定できる*

*定理*：$`\alpha` が同値 ⟺ 全ての頂点 $`k` で $`\alpha_k` が同値。後者のばらばらなデータから前者の整合した逆元と間を埋めるものが出る、という主張。

- *(⇒)*：$`\mathrm{ev}_k` は同型を保つ。

- *(⇐)*（Kerodon §4.4.4）：1 圏のように逆元を集めると高次の整合性の選択になるので、代わりに 3.2 の逆向き（最初の辺が $`\alpha` の $`\Lambda^n_0` が全て埋まれば同値）を使う。指数随伴で延長問題 $`\Lambda^n_0\times K\to\mathcal C` を $`\Delta^n\times K` へ（各 $`\{0\to1\}\times\{k\}` は同値）。$`K` の非退化単体を一つずつ付けて $`(\Lambda^n_0\times\Delta^m)\cup(\Delta^n\times\partial\Delta^m)\subseteq\Delta^n\times\Delta^m` に帰着（Kerodon Lemma 4.4.4.8）。この包含はホーン $`\Lambda^q_p`（$`0\le p\lt q`）の押し出しの列に分解でき、$`p=0` なら最初の辺は $`\{0\to1\}\times\{\text{頂点}\}` の形（Lemma 4.4.4.7：格子上の単調な道で、両方向に全射かつ $`(p,0)\to(p,1)` と縦に一歩進むものを、次元の小さい順・同じ次元では $`p` の大きい順に付ける）。内ホーンは準圏性、外ホーンは最初の辺が成分なので Joyal の定理で埋まる。

*帰結*：$`\mathrm{Fun}(K,\mathcal C)^{\simeq}` の辺は自然同値（3.3 の表の正当化）。模型 3 の写像空間は Kan（辺は両端の成分が恒等なので同値、相対版 Joyal で fiber の外ホーンが埋まる）。段 6・7 の「fiber ごとに同値なら同値」の原型。

*Lean での扱い*：形式化の証明は上とは別の組み立て。

1. $`\mathcal C` の同値な辺を頂点とする $`\mathrm{Fun}(\Delta^1,\mathcal C)` の充満部分複体 $`P`（\`equivalencePath\`、頂点条件 \`IsEquivalencePathVertex\`）と、その上の普遍ホモトピー \`equivalencePathHomotopy\` を作る。

2. 始点評価 $`P\to\mathcal C` は自明 Kan fibration（\`trivialKanFibration\_equivalencePathEndpoint\_zero\`、終点版 \`trivialKanFibration\_equivalencePathEndpoint\_one\`）。証明は境界上の角柱を「最初の縦の辺が同値な角柱の延長」（\`prism\_exists\_extension\_of\_invertible\_firstEdge\`：内ホーンは準圏性、$`\Lambda_0` は Joyal）で埋める。ここで角柱のセル分解が使われる。

3. 定値 path の切断 $`\mathcal C\to P` は圏同値で、前合成 $`\mathrm{Fun}(P,\mathcal C)\to\mathrm{Fun}(\mathcal C,\mathcal C)` は充満忠実。普遍ホモトピーの辺はそこで恒等に写るので同値（\`equivalencePathHomotopy\_edge\_isInvertible\`、反映は \`IsFullyFaithful.reflects\_isInvertibleEdge\`）。

4. 各点で同値な $`\alpha` は $`K\to P` を経由するので、普遍の場合の前合成として同値（\`functorEdgeOfSimplicialHomotopy\_isInvertible\_of\_pointwise\`）。

定理は \`isInvertibleEdge\_iff\_evaluateFunctorAt\`（\`Core/FunctorEdgePointwise.lean\`）、両端を任意の頂点にした版が \`isInvertibleEdge\_iff\_evaluateFunctorAt\_any\`（\`Core/EquivalencePathInternalHom.lean\`）。「普遍な場合に帰着して前合成する」方針で、Kerodon §4.5 の組み立てに近い。

:::

:::corollary "kerodon_4_4_4_6"
Kerodon Corollary 4.4.4.6（[Tag 01DM](https://kerodon.net/tag/01DM)）。対応表の状態：なし。

quasicategoryCoreProduct は比較射の構成だけで同型性・普遍性を述べない。指定関手の極限保存の特殊形を直接結論しない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.quasicategoryCoreProduct`

:::

:::lemma_ "kerodon_4_4_4_7" (uses := "kerodon_1_1_0_6, kerodon_3_1_2_11")
Kerodon Lemma 4.4.4.7（[Tag 01DN](https://kerodon.net/tag/01DN)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：普通の自然同型・二項積と core・一点と prismを照合。Δᵐ×Δⁿ の指定始辺を保つ外ホーン付き有限フィルトレーション。prism の既存分解は Δ¹ または別の境界を使う。

:::

:::lemma_ "kerodon_4_4_4_8" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_4_2_13, kerodon_4_4_4_7")
Kerodon Lemma 4.4.4.8（[Tag 01DP](https://kerodon.net/tag/01DP)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：普通の自然同型・二項積と core・一点と prismを照合。全頂点を含む A 上の相対ホーン図式を与え、各点のファイバーの辺が可逆なときの延長。一般の inner fibration での当該比較は未発見。

:::

:::proposition "kerodon_4_4_4_9" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_4_2_6, kerodon_4_4_4_8")
Kerodon Proposition 4.4.4.9（[Tag 023A](https://kerodon.net/tag/023A)）。対応表の状態：なし。

isInvertibleEdge\_vertexFiber\_iff はfiberの辺と全空間の辺の可逆性の比較。原文は底上の関手空間での可逆性と各評価fiberでの可逆性の比較で、Bが一点でも対象同定がさらに必要。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_vertexFiber_iff`

:::

# 4.4.5 Exponentiation for Isofibrations

%%%
number := false
tag := "kerodon-4-4-5"
%%%

Kerodon [Tag 01F0](https://kerodon.net/tag/01F0)

:::proposition "kerodon_4_4_5_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting.relativeInternalHom")
Kerodon Proposition 4.4.5.1（[Tag 01F1](https://kerodon.net/tag/01F1)）。対応表の状態：本体にある。

*主張*　同型ファイブレーション $`C\to D` と単体部分集合 $`A\subseteq B` に対し、$`\operatorname{Fun}(B,C)\to\operatorname{Fun}(A,C)\times_{\operatorname{Fun}(A,D)}\operatorname{Fun}(B,D)` も同型ファイブレーションである。

仮定：EquivalenceLifting を持つ U、単射 i、内部 Hom の引き戻しの選択（Kerodon と一致）。結論：Fun(B,C) から制限と U による後合成を組にした比較射が EquivalenceLifting（一致）。

:::

:::corollary "kerodon_4_4_5_3" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.equivalenceLifting_pre")
Kerodon Corollary 4.4.5.3（[Tag 01F3](https://kerodon.net/tag/01F3)）。対応表の状態：本体にある。

*主張*　無限圏 $`C` と単体部分集合 $`A\subseteq B` に対し、$`\operatorname{Fun}(B,C)\to\operatorname{Fun}(A,C)` は同型ファイブレーションである。

仮定：Quasicategory X と単射 i:A→B（Kerodon と一致）。結論：制限 (pre i).app X が EquivalenceLifting（一致）。

:::

:::corollary "kerodon_4_4_5_4" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.coreMap_fibration_of_kanEquivalenceLifting, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.equivalenceLifting_pre") (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_4_3_7, kerodon_4_4_5_3")
Kerodon Corollary 4.4.5.4（[Tag 01F4](https://kerodon.net/tag/01F4)）。対応表の状態：本体にある。

*主張*　無限圏 $`C` と単体部分集合 $`A\subseteq B` に対し、制限は芯の間の Kan ファイブレーション $`\operatorname{Fun}(B,C)^{\simeq}\to\operatorname{Fun}(A,C)^{\simeq}` を誘導する。

equivalenceLifting\_pre が同じ制限射にEquivalenceLiftingを返し、それをcoreMap\_fibration\_of\_kanEquivalenceLiftingにそのまま代入すると原文のcore制限射のKan fibration性を得る。仮定・対象・射が一致し追加の数学的比較は要らない。

:::

:::corollary "kerodon_4_4_5_5" (uses := "kerodon_1_4_0_1, kerodon_4_4_5_3")
Kerodon Corollary 4.4.5.5（[Tag 02QY](https://kerodon.net/tag/02QY)）。対応表の状態：なし。

二つの端点への各射影の自明Kan性は、両端の組への原文の射のisofibration性ではない。別の射の性質だけをcomponentにしない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.trivialKanFibration_equivalencePathEndpoint_zero`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.trivialKanFibration_equivalencePathEndpoint_one`

:::

:::corollary "kerodon_4_4_5_6" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting.internalHom")
Kerodon Corollary 4.4.5.6（[Tag 01H7](https://kerodon.net/tag/01H7)）。対応表の状態：本体にある。

*主張*　無限圏の同型ファイブレーション $`C\to D` と任意の単体集合 $`B` に対し、後合成 $`\operatorname{Fun}(B,C)\to\operatorname{Fun}(B,D)` は同型ファイブレーションである。

仮定：EquivalenceLifting を持つ U と任意の単体集合 K（Kerodon と一致）。結論：(ihom K).map U が EquivalenceLifting（一致）。

:::

:::corollary "kerodon_4_4_5_7" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.corePathReplacementMap_internalHom_fibration, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting.internalHom, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.coreMap_fibration_of_kanEquivalenceLifting") (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_4_4_3_7, kerodon_4_4_5_6")
Kerodon Corollary 4.4.5.7（[Tag 02QZ](https://kerodon.net/tag/02QZ)）。対応表の状態：本体にある。

*主張*　無限圏の同型ファイブレーション $`C\to D` と任意の単体集合 $`B` に対し、後合成は関手圏の芯の間の Kan ファイブレーションを誘導する。

EquivalenceLifting.internalHom に任意Bを代入し、coreMap\_fibration\_of\_kanEquivalenceLiftingをその結果に適用すると、原文の同じ内部Homのcore後合成のKan fibration性を得る。isofibrationとの比較は二条件のiffで確認済み。

:::

:::proposition "kerodon_4_4_5_8" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.prism_lift_boundary_with_final_endpoint") (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_3_1_2_12, kerodon_4_4_2_13, kerodon_4_4_4_8")
Kerodon Proposition 4.4.5.8（[Tag 01NX](https://kerodon.net/tag/01NX)）。対応表の状態：一部。

*主張*　無限圏の内部ファイブレーション $`F:C\to D` と、全頂点を含む単体部分集合 $`A\subseteq B` を取る。$`A` に入らない各単体の終頂点 $`b` で $`\Delta^1\times\{b\}` の像が同型なら、$`(\Delta^1\times A)\cup(\{1\}\times B)\to C` は $`D` 上の指定された $`\Delta^1\times B\to D` を持ち上げるように延長できる。

prism\_lift\_boundary\_with\_final\_endpoint は B=Δ\^(n+1)、A=その境界で最後の垂直辺が可逆な原文と同じprism持ち上げを直接返す。Aが全頂点を含む次元とその境界形に限る。

:::

:::corollary "kerodon_4_4_5_9" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_4_4_4, kerodon_4_4_5_8")
Kerodon Corollary 4.4.5.9（[Tag 01NY](https://kerodon.net/tag/01NY)）。対応表の状態：なし。

relativeEquivalencePathMapAtの自明Kan性は特定の可逆path空間の持ち上げ。原文の点ごとに可逆なprism全体をその空間に入れる比較と条件の同定を型で与えず、証明部品にとどまる。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeEquivalencePathMapAt_one_trivialKanFibration`

:::

:::corollary "kerodon_4_4_5_10" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.trivialKanFibration_equivalencePathEndpoint_zero, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.trivialKanFibration_equivalencePathEndpoint_one, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePath")
Kerodon Corollary 4.4.5.10（[Tag 02BY](https://kerodon.net/tag/02BY)）。対応表の状態：本体にある。

*主張*　無限圏の矢印圏で同型を対象とする充満部分圏から、始域または終域を取る二つの関手はともに自明な Kan ファイブレーションである。

仮定：Quasicategory X（Kerodon と一致）。結論：可逆辺が張る Fun(Δ¹,X) の全部分複体 equivalencePath X からの 0,1 での評価がともに自明 Kan ファイブレーション（一致）。

:::

:::definition "kerodon_4_4_5_11" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting.relativeInternalHom") (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1")
Kerodon Variant 4.4.5.11（[Tag 01NZ](https://kerodon.net/tag/01NZ)）。対応表の状態：一部。

*主張*　内部ファイブレーション $`C\to D` と全頂点を含む単体部分集合 $`A\subseteq B` に対し、$`\operatorname{Fun}(B,C)\to\operatorname{Fun}(A,C)\times_{\operatorname{Fun}(A,D)}\operatorname{Fun}(B,D)` は同型ファイブレーションである。

FにさらにEquivalenceLifting（isofibration）を仮定すると relativeInternalHom が同じ比較射F′のEquivalenceLiftingを直接返す。inner fibrationだけの場合は含まない。

:::

:::corollary "kerodon_4_4_5_12" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.kanEquivalenceLifting_relativeFunctorOverPre_of_cocartesian")
Kerodon Corollary 4.4.5.12（[Tag 069D](https://kerodon.net/tag/069D)）。対応表の状態：一部。

*主張*　無限圏の内部ファイブレーション $`C\to D`、単体図式 $`B\to D`、部分集合 $`A\subseteq B` に対し、$`D` 上での制限 $`\operatorname{Fun}_{/D}(B,C)\to\operatorname{Fun}_{/D}(A,C)` は同型ファイブレーションである。

kanEquivalenceLifting\_relativeFunctorOverPre\_of\_cocartesian はFがcocartesian fibrationである場合、同じ底上の関手空間の制限射のEquivalenceLiftingを直接返す。inner fibrationだけの場合は含まない。

:::

