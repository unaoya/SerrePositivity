import Verso
import VersoManual
import VersoBlueprint
import Mathlib.AlgebraicTopology.Quasicategory.Basic
import Mathlib.AlgebraicTopology.Quasicategory.TwoTruncated
import Mathlib.AlgebraicTopology.SimplicialSet.CompStruct
import Mathlib.AlgebraicTopology.SimplicialSet.CompStructTruncated
import Mathlib.AlgebraicTopology.SimplicialSet.HomotopyCat
import Mathlib.AlgebraicTopology.SimplicialSet.NerveAdjunction
import Mathlib.AlgebraicTopology.SimplicialSet.Op
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.InvertibleEdgeLifting
import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromCategoriesToSimplicialSets.KanCharacterization
import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.Checks
import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.HomotopyCategoryBridge
import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.HomotopyCategoryMap
import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.Opposite
import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.OuterHornConverse

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "1.4 ∞-Categories" =>
%%%
number := false
tag := "kerodon-1-4"
%%%

Kerodon の 1.4 節（[Tag 0039](https://kerodon.net/tag/0039)）の項目と、SerrePositivity・Mathlib の宣言との対応。本文は対応表（research/kerodon-coverage）の判定の理由の要約で、Kerodon の本文の写しではない。

:::definition "kerodon_1_4_0_1" (lean := "SSet.Quasicategory")
Kerodon Definition 1.4.0.1（[Tag 003A](https://kerodon.net/tag/003A)）。対応表の状態：Mathlib にある。

仮定：単体集合 X（Kerodon と一致）。結論：Quasicategory X は全ての内ホーン 0\<i\<n の充填条件（一致）。

:::

# 1.4.1 Objects and Morphisms

%%%
number := false
tag := "kerodon-1-4-1"
%%%

Kerodon [Tag 003F](https://kerodon.net/tag/003F)

:::definition "kerodon_1_4_1_1" (lean := "SSet.Edge")
Kerodon Definition 1.4.1.1（[Tag 003G](https://kerodon.net/tag/003G)）。対応表の状態：Mathlib にある。

仮定：準圏 X（Lean が弱い：Edge の定義は任意の単体集合で使える）。結論：対象は X₀ の元、Edge x y は d₁=x と d₀=y を指定した X₁ の元（一致）。

:::

:::definition "kerodon_1_4_1_2" (lean := "SSet.Edge")
Kerodon Notation 1.4.1.2（[Tag 003H](https://kerodon.net/tag/003H)）。対応表の状態：Mathlib にある。

仮定：準圏 X と二つの対象 x,y（Lean が弱い：Edge x y に準圏性は不要）。結論：x ⟶ y という記法の内容を、端点を指定した Edge x y で表す（一致）。

:::

:::definition "kerodon_1_4_1_5" (lean := "SSet.Edge")
Kerodon Definition 1.4.1.5（[Tag 03X3](https://kerodon.net/tag/03X3)）。対応表の状態：Mathlib にある。

仮定：準圏 X の対象 x（Lean が弱い：任意の単体集合の頂点でよい）。結論：Edge x x が始点と終点の等しい自己射を表す（一致）。

:::

# 1.4.2 The Opposite of an ∞-Category

%%%
number := false
tag := "kerodon-1-4-2"
%%%

Kerodon [Tag 003L](https://kerodon.net/tag/003L)

:::definition "kerodon_1_4_2_1"
Kerodon Notation 1.4.2.1（[Tag 003M](https://kerodon.net/tag/003M)）。対応表の状態：一部。

NonemptyFinLinOrdの双対は非空な有限線形順序だけ。原文のLinは空の順序も含む。

宣言：`NonemptyFinLinOrd`、`NonemptyFinLinOrd.dual`

:::

:::definition "kerodon_1_4_2_2" (lean := "SSet.opFunctor")
Kerodon Construction 1.4.2.2（[Tag 003N](https://kerodon.net/tag/003N)）。対応表の状態：Mathlib にある。

仮定：任意の単体集合 X（Kerodon と一致）。結論：opFunctor.obj X は単体圏の順序反転から誘導した関手で X を前合成した反対単体集合（一致）。

:::

:::proposition "kerodon_1_4_2_6" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.quasicategory_op, SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.hornReverseIso")
Kerodon Proposition 1.4.2.6（[Tag 003S](https://kerodon.net/tag/003S)）。対応表の状態：本体にある。

仮定：準圏 X（Kerodon と一致）。結論：quasicategory\_op は X.op が準圏であることを結論し、hornReverseIso がホーンの反転を与える（一致）。

:::

:::definition "kerodon_1_4_2_8"
Kerodon Variant 1.4.2.8（[Tag 050H](https://kerodon.net/tag/050H)）。対応表の状態：Mathlib にある。

仮定：Kan 複体 X（Kerodon と一致）。結論：instKanComplexOp は X.op の KanComplex インスタンスを与える（一致）。

宣言：`SSet.instKanComplexOp`

:::

# 1.4.3 Homotopies of Morphisms

%%%
number := false
tag := "kerodon-1-4-3"
%%%

Kerodon [Tag 003U](https://kerodon.net/tag/003U)

:::definition "kerodon_1_4_3_1" (lean := "SSet.Truncated.HomotopicL")
Kerodon Definition 1.4.3.1（[Tag 003V](https://kerodon.net/tag/003V)）。対応表の状態：Mathlib にある。

仮定：準圏 X の同じ端点を持つ二辺 f,g（Lean が弱い：HomotopicL の定義は 2 切断上の辺だけでよい）。結論：d₂=f、d₁=g、d₀=id を満たす 2 単体の存在で f と g の左ホモトピーを表す（一致）。

:::

:::proposition "kerodon_1_4_3_5" (lean := "SSet.Truncated.HomotopicL.refl, SSet.Truncated.HomotopicL.symm, SSet.Truncated.HomotopicL.trans")
Kerodon Proposition 1.4.3.5（[Tag 003Z](https://kerodon.net/tag/003Z)）。対応表の状態：Mathlib にある。

仮定：準圏 X の固定端点 x,y（Kerodon と一致。Lean の Quasicategory₂ は X の 2 切断に供給される）。結論：HomotopicL.refl・symm・trans は Edge x y のホモトピーが同値関係であることを与える（一致）。

:::

:::proposition "kerodon_1_4_3_6" (lean := "SSet.Truncated.homotopicL_iff_homotopicR")
Kerodon Proposition 1.4.3.6（[Tag 0040](https://kerodon.net/tag/0040)）。対応表の状態：Mathlib にある。

仮定：準圏 X と平行な辺 f,g（Kerodon と一致。Lean は 2 切断上で述べる）。結論：homotopicL\_iff\_homotopicR は終点側の恒等辺を持つホモトピーと始点側の恒等辺を持つホモトピーを同値とする。原文の反対準圏での条件が後者（一致）。

:::

:::corollary "kerodon_1_4_3_7"
Kerodon Corollary 1.4.3.7（[Tag 00V0](https://kerodon.net/tag/00V0)）。対応表の状態：一部。

引用先はホモトピー圏での四辺の可換性から指定辺を保つ正方形ホモトピーを得る方向。原文の両方向の同値としての宣言ではない。完全名を補正。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.exists_arrowHomotopy_of_homMk_comm`

:::

# 1.4.4 Composition of Morphisms

%%%
number := false
tag := "kerodon-1-4-4"
%%%

Kerodon [Tag 0041](https://kerodon.net/tag/0041)

:::definition "kerodon_1_4_4_1" (lean := "SSet.Edge.CompStruct, SSet.Truncated.Edge.CompStruct")
Kerodon Definition 1.4.4.1（[Tag 0042](https://kerodon.net/tag/0042)）。対応表の状態：Mathlib にある。

仮定：準圏の可合成な辺 f,g と同じ両端を持つ候補 h（Lean が弱い：CompStruct は任意の単体集合または 2 切断に定義できる）。結論：CompStruct f g h は d₂=f、d₀=g、d₁=h の 2 単体を証人として持つ（一致）。

:::

:::proposition "kerodon_1_4_4_2" (lean := "SSet.Truncated.Edge.CompStruct.comp_unique, SSet.Truncated.Edge.CompStruct.nonempty_iff")
Kerodon Proposition 1.4.4.2（[Tag 0043](https://kerodon.net/tag/0043)）。対応表の状態：Mathlib にある。

仮定：準圏の可合成な辺 f,g（Kerodon と一致。2 切断には Quasicategory₂ が入る）。結論：fill21 が合成の存在、comp\_unique が二つの合成のホモトピーを与える。CompStruct.nonempty\_iff は合成の証人の存在とホモトピー類での合成等式を結び、ホモトピックな候補の逆方向を与える（一致）。

:::

:::definition "kerodon_1_4_4_3" (lean := "SSet.Truncated.Edge.comp, SSet.Truncated.Edge.compStruct")
Kerodon Notation 1.4.4.3（[Tag 0044](https://kerodon.net/tag/0044)）。対応表の状態：Mathlib にある。

仮定：準圏の可合成な辺 f,g（Kerodon と一致。Lean は 2 切断で選択）。結論：Edge.comp が合成辺を選び、compStruct が対応する 2 単体を与える（一致）。

:::

:::proposition "kerodon_1_4_4_7" (lean := "SSet.Truncated.Edge.CompStruct.comp_unique")
Kerodon Proposition 1.4.4.7（[Tag 0048](https://kerodon.net/tag/0048)）。対応表の状態：Mathlib にある。

仮定：二組の可合成な辺 f,g と f′,g′、各辺のホモトピー、両組の合成の証人（Kerodon と一致）。結論：comp\_unique はその二つの合成辺の HomotopicL を結論する（一致）。

:::

# 1.4.5 The Homotopy Category of an ∞-Category

%%%
number := false
tag := "kerodon-1-4-5"
%%%

Kerodon [Tag 0049](https://kerodon.net/tag/0049)

:::definition "kerodon_1_4_5_1" (lean := "SSet.Truncated.HomotopyCategory₂.Hom, SSet.Truncated.instSetoidEdge")
Kerodon Construction 1.4.5.1（[Tag 004A](https://kerodon.net/tag/004A)）。対応表の状態：Mathlib にある。

仮定：準圏 X と頂点 x,y（Kerodon と一致。Lean は 2 切断の準圏構造を使う）。結論：HomotopyCategory₂.Hom x y は Edge x y を HomotopicL で割った商で、instSetoidEdge がその同値関係を与える（一致）。

:::

:::proposition "kerodon_1_4_5_2"
Kerodon Proposition 1.4.5.2（[Tag 004B](https://kerodon.net/tag/004B)）。対応表の状態：Mathlib にある。

仮定：準圏 X（Kerodon と一致。Lean は 2 切断で圏構造を作る）。結論：instCategoryHomotopyCategory₂ の assoc と id\_comp・comp\_id が、辺の類の合成の結合律と恒等辺の類の左右単位律を与える（一致）。

宣言：`SSet.Truncated.instCategoryHomotopyCategory₂`

:::

:::definition "kerodon_1_4_5_3" (lean := "SSet.Truncated.HomotopyCategory₂, SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyCategoryBridge, SSet.hoFunctor")
Kerodon Definition 1.4.5.3（[Tag 004C](https://kerodon.net/tag/004C)）。対応表の状態：本体と Mathlib にある。

仮定：準圏 X（Kerodon と一致）。結論：HomotopyCategory₂ は頂点と辺のホモトピー類の圏。homotopyCategoryBridge はこれを hoFunctor.obj X に比較する（一致）。

:::

:::proposition "kerodon_1_4_5_4" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.nerveHomotopyCategoryEquivalence, CategoryTheory.nerveFunctorCompHoFunctorIso")
Kerodon Example 1.4.5.4（[Tag 004D](https://kerodon.net/tag/004D)）。対応表の状態：本体と Mathlib にある。

仮定：通常の圏 C（Kerodon と一致）。結論：nerveHomotopyCategoryEquivalence と nerveFunctorCompHoFunctorIso は hN(C) と C を比較する。C=\[n\] の場合に標準単体の主張になる（一致）。

:::

:::definition "kerodon_1_4_5_6"
Kerodon Construction 1.4.5.6（[Tag 004G](https://kerodon.net/tag/004G)）。対応表の状態：一部。

2単体の合成関係はnonempty\_iffが表す。原文の全n単体に対する標準写像u:C→N(hC)そのものの構成は引用されていない。

宣言：`SSet.Truncated.Edge.CompStruct.nonempty_iff`、`SSet.stdSimplex.isoNerve`

:::

:::proposition "kerodon_1_4_5_7" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyCategoryBridge, SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.bridge_naturality")
Kerodon Proposition 1.4.5.7（[Tag 004H](https://kerodon.net/tag/004H)）。対応表の状態：本体にある。

仮定：準圏 X と通常圏 D。原文ではさらに 1.4.5.6 の指定写像 u を使う（Kerodon と一致するのは X の準圏性）。結論：homotopyCategoryBridge と bridge\_naturality は二つのホモトピー圏モデルの自然な比較を与える（Lean が弱い：引用の型では指定 u に沿う Fun(hX,D) と Hom(X,N(D)) の全単射を直接確認できない）。

:::

# 1.4.6 Isomorphisms

%%%
number := false
tag := "kerodon-1-4-6"
%%%

Kerodon [Tag 004Q](https://kerodon.net/tag/004Q)

:::definition "kerodon_1_4_6_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge")
Kerodon Definition 1.4.6.1（[Tag 004R](https://kerodon.net/tag/004R)）。対応表の状態：本体にある。

仮定：準圏 X の辺 f（Lean が弱い：IsInvertibleEdge 自体は準圏性を要求しない）。結論：2 切断の HomotopyCategory.homMk f が IsIso であることを述べ、準圏のホモトピー圏で f の類が同型となる条件に対応する（一致）。

:::

:::definition "kerodon_1_4_6_4" (lean := "SSet.Edge.InvStruct, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge.nonempty_inverse")
Kerodon Definition 1.4.6.4（[Tag 004V](https://kerodon.net/tag/004V)）。対応表の状態：本体と Mathlib にある。

仮定：準圏 X の辺 f:x→y と逆向きの辺 g（Lean が弱い：InvStruct の構造自体は一般の単体集合上）。結論：InvStruct は同じ g と f の二つの合成が各恒等辺となる 2 単体を持ち、nonempty\_inverse は可逆辺からその両側の証人を取り出す（一致）。

:::

:::proposition "kerodon_1_4_6_10" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.kanComplex_ho_isGroupoid, SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromCategoriesToSimplicialSets.kanComplex_iff_isGroupoid")
Kerodon Proposition 1.4.6.10（[Tag 0052](https://kerodon.net/tag/0052)）。対応表の状態：本体にある。

仮定：Kan 複体 X（Kerodon と一致）。結論：kanComplex\_ho\_isGroupoid は hoFunctor.obj X に IsGroupoid を与えるので、全辺のホモトピー類が同型。kanComplex\_iff\_isGroupoid は準圏上の逆も与える（Lean が強い：特徴付けまで含む）。

:::

:::definition "kerodon_1_4_6_12" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.kanComplex_ho_isGroupoid")
Kerodon Definition 1.4.6.12（[Tag 00HZ](https://kerodon.net/tag/00HZ)）。対応表の状態：本体にある。

仮定：Kan 複体 X（Kerodon と一致）。結論：kanComplex\_ho\_isGroupoid は Kan 複体のホモトピー圏が亜群であることを与え、これが原文の基本亜群 π≤1(X) に当たる（一致）。

:::

