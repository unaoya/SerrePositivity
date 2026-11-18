import Verso
import VersoManual
import VersoBlueprint
import Mathlib.CategoryTheory.Bicategory.Grothendieck
import Mathlib.CategoryTheory.Grothendieck
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftUnstraightening
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftUnstraighteningFiberIso

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "5.6 Classification of Cocartesian Fibrations" =>
%%%
number := false
tag := "kerodon-5-6"
%%%

Kerodon の 5.6 節（[Tag 027M](https://kerodon.net/tag/027M)）の項目と、SerrePositivity・Mathlib の宣言との対応。本文は対応表（research/kerodon-coverage）の判定の理由の要約で、Kerodon の本文の写しではない。

*定義 11.2 （小さいファイバー）*

単体的集合の射 $`q\colon E\to B` が小さいファイバーをもつとは、$`B` のすべての頂点 $`b` について、ファイバー $`E_b`（定義 6.2）が小さい（冒頭の規約）ことをいう。

*注意 （直観と大きさ）*

$`\mathrm{St}(q)` は頂点 $`b` をファイバー $`E_b` に、辺 $`b\to b'` を左 fibration の持ち上げで得られる $`E_b\to E_{b'}` に送る関手である。$`\mathcal S` の対象は小さい Kan 複体なので、値が $`\mathcal S` に入るためにファイバーが小さいことを仮定する。$`B` は quasicategory でなくてよく、大きさも問わない。

:::theorem "kerodon_5_6_0_2" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_5_1_4_1, kerodon_5_6_5_12, kerodon_5_6_5_15")
Kerodon Theorem 5.6.0.2（[Tag 028K](https://kerodon.net/tag/028K)）。対応表の状態：なし。

有限鎖上のcocartesianStraighteningCoherentMapの圏同値はあるが、原文の指定積分の構成と相対fibration同値類・Functor coreのπ₀の全単射へ比較する型がない。分類の模型の同値だけをそのまま数えない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStraighteningCoherentMap_finite_isQCatEquivalence`

:::

:::corollary "kerodon_5_6_0_6" (uses := "kerodon_1_1_0_6")
Kerodon Corollary 5.6.0.6（[Tag 028T](https://kerodon.net/tag/028T)）。対応表の状態：一部。

底Cを準圏に強めればleftStraighteningInfinityMap\_isQCatEquivalenceはleft fibrationと空間値図式の同じ分類の∞圏同値を直接与える。従ってcoreの頂点の同型類の全単射を与える。非準圏の底の単射側は含まない。

*定義 11.3 （straightening）*

単体的集合 $`B` 上の左 fibration（定義 5.3）$`q\colon E\to B` で小さいファイバーをもつもの（定義 11.2）に、関手（定義 11.1）

$$`\mathrm{St}(q)\colon B\to\mathcal S`

を対応させる操作を straightening という（$`\mathcal S` は定義 3.7）。構成は後の章で与える。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityMap_isQCatEquivalence`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityMap_isEssentiallySurjective`

:::

# 5.6.1 Elements of Category-Valued Functors

%%%
number := false
tag := "kerodon-5-6-1"
%%%

Kerodon [Tag 01R1](https://kerodon.net/tag/01R1)

:::definition "kerodon_5_6_1_1" (lean := "CategoryTheory.Pseudofunctor.Grothendieck, CategoryTheory.Pseudofunctor.Grothendieck.category, CategoryTheory.Grothendieck")
Kerodon Definition 5.6.1.1（[Tag 025N](https://kerodon.net/tag/025N)）。対応表の状態：Mathlib にある。

仮定：通常の圏 C と LocallyDiscrete C から Cat への擬関手 F（Kerodon と一致）。結論：Grothendieck F は (c,x) を対象とし、射は (f:c→d, F(f)(x)→y)。通常の Cat 値関手の版もある（一致）。

:::

:::proposition "kerodon_5_6_1_3" (lean := "CategoryTheory.Pseudofunctor.Grothendieck.category")
Kerodon Proposition 5.6.1.3（[Tag 01R3](https://kerodon.net/tag/01R3)）。対応表の状態：Mathlib にある。

仮定：通常の圏 C と Cat 値擬関手 F（Kerodon と一致）。結論：指定された Grothendieck F の合成に対して恒等則と結合則を持つ Category instance（一致）。

:::

:::definition "kerodon_5_6_1_5" (lean := "CategoryTheory.Pseudofunctor.CoGrothendieck, CategoryTheory.Pseudofunctor.CoGrothendieck.category")
Kerodon Definition 5.6.1.5（[Tag 025P](https://kerodon.net/tag/025P)）。対応表の状態：Mathlib にある。

仮定：通常の圏 C の反対圏から Cat への擬関手 F（Kerodon と一致）。結論：CoGrothendieck F は (c,x) と (f:c→d, x→F(f)(y)) による圏（一致）。

:::

:::definition "kerodon_5_6_1_12" (lean := "CategoryTheory.Pseudofunctor.Grothendieck.forget, CategoryTheory.Pseudofunctor.CoGrothendieck.forget")
Kerodon Notation 5.6.1.12（[Tag 01RA](https://kerodon.net/tag/01RA)）。対応表の状態：Mathlib にある。

仮定：通常の圏 C から、または Cᵒᵖ からの Cat 値擬関手 F（Kerodon と一致）。結論：共変・反変の Grothendieck 構成に対して、対象と射を底の成分に送る forget 関手（一致）。

:::

:::proposition "kerodon_5_6_1_16"
Kerodon Proposition 5.6.1.16（[Tag 025S](https://kerodon.net/tag/025S)）。対応表の状態：なし。

Mathlibの型は反変CoGrothendieckの選んだcartesian lift。原文の共変Grothendieckの一般(f,u)のcocartesian性とuの同型性のiffとは別の射と述語。

宣言：`CategoryTheory.Pseudofunctor.CoGrothendieck.isStronglyCartesian_homCartesianLift`

:::

:::corollary "kerodon_5_6_1_17"
Kerodon Corollary 5.6.1.17（[Tag 025T](https://kerodon.net/tag/025T)）。対応表の状態：一部。

MathlibのCoGrothendieck忘却のIsFibered instanceは原文後半の反変版射影がcartesian fibrationという結論そのもの。共変版は含まない。

宣言：`CategoryTheory.Pseudofunctor.CoGrothendieck.isStronglyCartesian_homCartesianLift`、`CategoryTheory.Pseudofunctor.CoGrothendieck.instIsFiberedForget`

:::

# 5.6.2 Elements of QC-Valued Functors

%%%
number := false
tag := "kerodon-5-6-2"
%%%

Kerodon [Tag 026H](https://kerodon.net/tag/026H)

:::definition "kerodon_5_6_2_1" (uses := "kerodon_1_1_0_6")
Kerodon Definition 5.6.2.1（[Tag 026J](https://kerodon.net/tag/026J)）。対応表の状態：なし。

leftUnstraighteningはSpaceInfinityとpointedSpaceProjectionのpullback。原文のN\^hc(Set\_Δ)とそのΔ⁰-cosliceのpullbackとは別の対象で、二つの普遍射影を比較する型がない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraightening`

:::

:::proposition "kerodon_5_6_2_2" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_5_1_4_1, kerodon_5_5_5_10, kerodon_5_5_5_11")
Kerodon Proposition 5.6.2.2（[Tag 026K](https://kerodon.net/tag/026K)）。対応表の状態：なし。

引用は空間の普遍left fibrationのpullback。原文のQC\_Objの普遍cocartesian fibrationとのpullback比較がなく、QC値の同じ積分の特殊形だと直接同定できない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection_leftFibration`

:::

:::corollary "kerodon_5_6_2_3"
Kerodon Corollary 5.6.2.3（[Tag 026L](https://kerodon.net/tag/026L)）。対応表の状態：なし。

leftUnstraightening\_quasicategoryは空間の普遍射影のpullbackの準圏性。原文のQC\_Objによる積分と同じ対象になる比較がない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraightening_quasicategory`

:::

:::definition "kerodon_5_6_2_4"
Kerodon Definition 5.6.2.4（[Tag 026M](https://kerodon.net/tag/026M)）。対応表の状態：なし。

SpaceInfinityによるleftUnstraighteningは原文のQC値の積分の定義と値域・普遍射影が異なり、指定対象を同定する比較がない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraightening`

:::

:::proposition "kerodon_5_6_2_5"
Kerodon Remark 5.6.2.5（[Tag 026N](https://kerodon.net/tag/026N)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Space 値・底辺ごとの比較・通常圏 Grothendieck と nerve・全図式の自然性を照合。通常圏上の strictly unital Cat 値図式の ∞ 版 Grothendieck 構成と通常の圏 of elements の nerve の標準同型。番号引用の base change や vertexFiberPullback はこの nerve 比較を述べない。

:::

:::proposition "kerodon_5_6_2_9" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraightening, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection_leftFibration, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningFiberIso")
Kerodon Example 5.6.2.9（[Tag 026S](https://kerodon.net/tag/026S)）。対応表の状態：本体にある。

仮定：任意の単体集合 C と F:C→SpaceInfinity（Kerodon と一致）。結論：PointedSpaceInfinity→SpaceInfinity を F に沿って引き戻した leftUnstraightening とその左ファイブレーション射影（一致）。

:::

:::proposition "kerodon_5_6_2_21" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_5_1_4_1, kerodon_5_1_7_1, kerodon_5_1_7_11, kerodon_5_5_5_11")
Kerodon Proposition 5.6.2.21（[Tag 02S7](https://kerodon.net/tag/02S7)）。対応表の状態：なし。

leftUnstraighteningMapは図式の厳密等式で与えた底変換の射。原文のFunctor空間の同型から底上の相対逆を持つ比較を返す型ではない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningMap`

:::

:::proposition "kerodon_5_6_2_22" (uses := "kerodon_1_4_0_1, kerodon_5_1_4_1, kerodon_5_2_8_9, kerodon_5_5_5_14")
Kerodon Proposition 5.6.2.22（[Tag 02S8](https://kerodon.net/tag/02S8)）。対応表の状態：なし。

leftStraighteningInfinityCounitは分類図式間のFunctorIso。原文の指定した比較θ\_Cと豊穣homotopyTransportの自然同型に結ぶ型がなく、別のunit/counitだけを数えない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityCounit`

:::

:::corollary "kerodon_5_6_2_23"
Kerodon Corollary 5.6.2.23（[Tag 027K](https://kerodon.net/tag/027K)）。対応表の状態：なし。

引用はstraightening counitとfiber同値を束ねたLeftTransportRepresentation。原文の各辺の作用・任意の選んだ共変輸送と指定θ\_Cからなる四角の可換性の型はない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityCounit`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation`

:::

:::corollary "kerodon_5_6_2_24" (uses := "kerodon_1_1_0_6")
Kerodon Corollary 5.6.2.24（[Tag 027L](https://kerodon.net/tag/027L)）。対応表の状態：なし。

引用はFunctor空間の辺F→Gをunstraighteningの全空間射へ移し、その各bの作用をpointed-space輸送と比較する。原文の一つのFの底の辺C→DとhC上の自然性とは異なる図式。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningEdgeMap_pointedFiberTransportIso`

:::

# 5.6.3 Comparison with the Category of Elements

%%%
number := false
tag := "kerodon-5-6-3"
%%%

Kerodon [Tag 0273](https://kerodon.net/tag/0273)

:::proposition "kerodon_5_6_3_1"
Kerodon Proposition 5.6.3.1（[Tag 0274](https://kerodon.net/tag/0274)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Set 値の圏 of elements・普通の nerve 比較・Space 値の特例を照合。∞ 版 ∫\_C F から通常 Grothendieck 圏の nerve への指定 T の一意性。weighted nerve の射影にはこの通常圏への比較がない。

:::

:::proposition "kerodon_5_6_3_2"
Kerodon Proposition 5.6.3.2（[Tag 0275](https://kerodon.net/tag/0275)）。対応表の状態：なし。

grothendieckTypeToCatは通常圏の二つの構成の圏同値。原文の積分のホモトピー圏からの指定した厳密同型との比較がない。

宣言：`CategoryTheory.Grothendieck.grothendieckTypeToCat`

:::

:::corollary "kerodon_5_6_3_3"
Kerodon Corollary 5.6.3.3（[Tag 027Y](https://kerodon.net/tag/027Y)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Set 値の圏 of elements・普通の nerve 比較・Space 値の特例を照合。left covering を hC 上の通常圏 of elements で判定する二条件。LeftFibration の分類は離散ファイバーの厳密な covering 判定ではない。

:::

:::proposition "kerodon_5_6_3_4"
Kerodon Proposition 5.6.3.4（[Tag 0276](https://kerodon.net/tag/0276)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Set 値の圏 of elements・普通の nerve 比較・Space 値の特例を照合。通常圏上の strictly unital Cat 値図式で ∞ 版 ∫ の nerve 比較 T が同型。一般の weighted nerve の定値図式比較は任意の bicategorical 図式を扱わない。

:::

:::corollary "kerodon_5_6_3_5"
Kerodon Corollary 5.6.3.5（[Tag 0278](https://kerodon.net/tag/0278)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Set 値の圏 of elements・普通の nerve 比較・Space 値の特例を照合。通常の Cat の pith に由来する図式について ∫\_C F の射影の性質を強める結果。一般の cocartesian straightening の型にこの因子化がない。

:::

# 5.6.4 Comparison with the Weighted Nerve

%%%
number := false
tag := "kerodon-5-6-4"
%%%

Kerodon [Tag 0279](https://kerodon.net/tag/0279)

:::definition "kerodon_5_6_4_1" (uses := "kerodon_1_1_0_6")
Kerodon Construction 5.6.4.1（[Tag 027A](https://kerodon.net/tag/027A)）。対応表の状態：なし。

exists\_kanWeightedUnstraighteningUnitはKan値図式に対する選択された比較の存在、reversed比較は反転した係数。原文のmin(S\\\{x\})による指定θの単体上の公式との比較がなく、同じ構成の特殊形ではない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.exists_kanWeightedUnstraighteningUnit`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallReversedWeightedKanUnstraighteningComparison`

:::

:::proposition "kerodon_5_6_4_8" (uses := "kerodon_1_4_0_1, kerodon_4_6_7_8, kerodon_5_1_1_1, kerodon_5_1_4_1, kerodon_5_1_6_1, kerodon_5_3_3_16, kerodon_5_6_2_2")
Kerodon Proposition 5.6.4.8（[Tag 027J](https://kerodon.net/tag/027J)）。対応表の状態：なし。

strictKanUnstraighteningComparisonの始域係数はsHom(Δ⁰,F(c))の反転、原文はF(c)そのもの。原文の指定θとの比較式がないため、反転模型上の同値を同じ射の結論として数えない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictKanUnstraighteningComparison`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictKanUnstraighteningComparison_isPrecompositionEquivalence`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictKanUnstraighteningComparison_projection`

:::

# 5.6.5 The Universality Theorem

%%%
number := false
tag := "kerodon-5-6-5"
%%%

Kerodon [Tag 028U](https://kerodon.net/tag/028U)

:::definition "kerodon_5_6_5_1" (uses := "kerodon_1_1_0_6, kerodon_5_1_4_1, kerodon_5_1_7_1")
Kerodon Definition 5.6.5.1（[Tag 028V](https://kerodon.net/tag/028V)）。対応表の状態：なし。

LeftTransportRepresentationはSpaceInfinity値とfiberごとの同値を束ねる。原文のQC\_Objによる四角と相対逆を持つ比較射の定義への同定がなく、類似の表現データにとどまる。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation`

:::

:::theorem "kerodon_5_6_5_12" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_3_2_7_2, kerodon_5_1_4_1, kerodon_5_6_8_3, kerodon_5_6_8_10")
Kerodon Theorem 5.6.5.12（[Tag 0293](https://kerodon.net/tag/0293)）。対応表の状態：なし。

引用はSpaceInfinity・pointed-spaceによるleft transport表現の厳密延長。原文のQC\_Objによる指定四角と同じ表現空間になる比較がない。任意の余デカルト表現をそのまま延長しない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.exists_coherentUnstraighteningRepresentation_extension`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.exists_smallFiber_leftTransportRepresentation_extension`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentUnstraighteningWitnessRestriction_trivialKanFibration`

:::

:::corollary "kerodon_5_6_5_13" (uses := "kerodon_1_1_0_6, kerodon_5_1_4_1")
Kerodon Corollary 5.6.5.13（[Tag 0294](https://kerodon.net/tag/0294)）。対応表の状態：なし。

引用の延長は空間値のleft transport表現で、原文のQC値表現の指定射影との比較がない。left fibrationに制限しても、与えられたQC値表現が同じ空間値データとは限らない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.exists_smallFiber_leftTransportRepresentation_extension`

:::

:::corollary "kerodon_5_6_5_14" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_5_1_4_1, kerodon_5_6_5_13")
Kerodon Corollary 5.6.5.14（[Tag 0295](https://kerodon.net/tag/0295)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Kan/Space 値の分類・通常圏の Grothendieck・充満部分圏・各頂点を照合。全ファイバーに同値な代表を含む充満部分圏 Q へ分類関手を落とす存在。Space 値の small unstraightening は任意の Q への因子化を与えない。

:::

:::corollary "kerodon_5_6_5_15" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_4_4_4, kerodon_5_1_4_1, kerodon_5_6_5_13")
Kerodon Corollary 5.6.5.15（[Tag 0296](https://kerodon.net/tag/0296)）。対応表の状態：なし。

空間値のtransportWitnessSpaceが可縮という型は、原文の任意の二つのQC値表現の間のFunctorIsoを直接返さない。表現の値域・証人空間の比較を欠く。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallTransportWitnessSpace_isContractibleKan`

:::

:::definition "kerodon_5_6_5_16" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_5_1_4_1, kerodon_5_6_5_14, kerodon_5_6_5_15")
Kerodon Notation 5.6.5.16（[Tag 019S](https://kerodon.net/tag/019S)）。対応表の状態：なし。

leftStraighteningInfinityMapと表現のnonemptyは空間値の構成。原文のQC値の表現の全同型類と、同型な任意候補も表現である条件への比較がない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityMap`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftTransportRepresentation_nonempty`

:::

:::corollary "kerodon_5_6_5_18" (uses := "kerodon_1_4_0_1, kerodon_5_3_5_6, kerodon_5_6_0_2")
Kerodon Corollary 5.6.5.18（[Tag 0387](https://kerodon.net/tag/0387)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Kan/Space 値の分類・通常圏の Grothendieck・充満部分圏・各頂点を照合。通常の小圏 C について hc nerve が原文の指定した図式の二集合の間に全単射を誘導する結論。coherentProduct の比較同値は指定集合の全単射を与えない。

:::

:::proposition "kerodon_5_6_5_20"
Kerodon Proposition 5.6.5.20（[Tag 029A](https://kerodon.net/tag/029A)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Kan/Space 値の分類・通常圏の Grothendieck・充満部分圏・各頂点を照合。inner covering と所定の Q を通る ∫\_C F の厳密同型による分類。内ファイブレーションの底上の ∞ 圏同値と、ここでの covering の厳密同型は区別した。

:::

:::corollary "kerodon_5_6_5_21"
Kerodon Corollary 5.6.5.21（[Tag 01SU](https://kerodon.net/tag/01SU)）。対応表の状態：なし。

Grothendieckの型と反変射影のfibered instanceだけでは、原文の与えられた共変fibrationを指定同型で復元するiffのいずれの方向も直接返さない。

宣言：`CategoryTheory.Pseudofunctor.Grothendieck`、`CategoryTheory.Pseudofunctor.CoGrothendieck.instIsFiberedForget`

:::

:::corollary "kerodon_5_6_5_22"
Kerodon Corollary 5.6.5.22（[Tag 01SZ](https://kerodon.net/tag/01SZ)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Kan/Space 値の分類・通常圏の Grothendieck・充満部分圏・各頂点を照合。通常の groupoid opfibration と Cat 値図式の Grothendieck 構成に同型であることの同値。Mathlib の Grothendieck は分裂の構成を与えるがこの分類を述べない。

:::

# 5.6.6 Application: Corepresentable Functors

%%%
number := false
tag := "kerodon-5-6-6"
%%%

Kerodon [Tag 02HU](https://kerodon.net/tag/02HU)

:::definition "kerodon_5_6_6_1" (uses := "kerodon_1_2_5_1, kerodon_1_4_0_1")
Kerodon Definition 5.6.6.1（[Tag 038A](https://kerodon.net/tag/038A)）。対応表の状態：なし。

IsCorepresentableSmallSpaceFunctorは共変Hom関手とのFunctorIsoの存在。原文は指定頂点xで評価した同じ写像空間作用の同値性であり、その頂点による同値との比較が型にない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.IsCorepresentableSmallSpaceFunctor`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.covariantRepresentableInfinity`

:::

:::definition "kerodon_5_6_6_2" (uses := "kerodon_1_4_0_1, kerodon_5_6_6_1")
Kerodon Variant 5.6.6.2（[Tag 038B](https://kerodon.net/tag/038B)）。対応表の状態：なし。

representablePresheafInfinityはHom前層の構成。原文の指定頂点が表現を与える述語とその存在の定義は直接与えない。

*定義 14.3 （表現可能前層）*

小さい quasicategory $`C` の頂点 $`y` について、前層 $`h_y` を合成

$$`h_y\colon C^{\mathrm{op}}\cong C^{\mathrm{op}}\times\Delta^0\xrightarrow{\ \mathrm{id}\times y\ }C^{\mathrm{op}}\times C\xrightarrow{\ \mathrm{Map}_C\ }\mathcal S`

で定め、$`y` が表現する前層という（$`\mathrm{Map}_C` は定義 12.5）。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafInfinity`

:::

:::definition "kerodon_5_6_6_10" (uses := "kerodon_1_2_5_1, kerodon_3_1_5_10")
Kerodon Definition 5.6.6.10（[Tag 02FR](https://kerodon.net/tag/02FR)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：点付き左ファイブレーションの特例・局所 Kan・通常の Yoneda・反対と輸送を照合。hKan 豊穣圏と反対圏での指定した表現可能関手の関係。通常の EnrichedCategory の Hom と op の定義だけでは hKan 値の比較がない。

:::

:::theorem "kerodon_5_6_6_13" (uses := "kerodon_1_4_0_1, kerodon_4_7_3_20, kerodon_5_1_7_1, kerodon_5_6_0_6, kerodon_5_6_6_19, kerodon_5_6_6_21")
Kerodon Theorem 5.6.6.13（[Tag 038J](https://kerodon.net/tag/038J)）。対応表の状態：なし。

共変Hom関手とcoslice分類の同型はあるが、原文の指定頂点でのcorepresentabilityとその存在・一意性を返す型へ比較されていない。関手があるだけを表現可能性の証明としない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.covariantRepresentableInfinity`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.covariantCosliceClassificationIso`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.covariantHomIsoOfCosliceEquivalence`

:::

:::definition "kerodon_5_6_6_14" (uses := "kerodon_1_4_0_1, kerodon_5_6_6_13")
Kerodon Notation 5.6.6.14（[Tag 038L](https://kerodon.net/tag/038L)）。対応表の状態：一部。

homInfinityCovariantとcovariantRepresentableInfinityは原文の共変Hom(X,−)の候補を具体的な図式として直接構成する。指定頂点によるcorepresentabilityと局所小な大きいC全体、二変数での比較は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.homInfinityCovariant`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.covariantRepresentableInfinity`

:::

:::proposition "kerodon_5_6_6_17" (uses := "kerodon_1_2_5_1, kerodon_4_6_7_3, kerodon_4_6_7_5, kerodon_5_6_6_1")
Kerodon Proposition 5.6.6.17（[Tag 038P](https://kerodon.net/tag/038P)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：点付き左ファイブレーションの特例・局所 Kan・通常の Yoneda・反対と輸送を照合。hc nerve 上の Space 値関手を、指定点が representable にするための条件。Yoneda の普遍性や一点の評価だけではこの enriched 側の特徴付けが出ない。

:::

:::proposition "kerodon_5_6_6_19" (uses := "kerodon_1_4_0_1, kerodon_4_2_5_4, kerodon_4_7_3_1, kerodon_4_7_3_9, kerodon_4_7_3_20, kerodon_4_7_3_22, kerodon_5_1_7_5")
Kerodon Proposition 5.6.6.19（[Tag 038R](https://kerodon.net/tag/038R)）。対応表の状態：なし。

IsInitialVertex.exists\_cosliceLiftは始対象から任意A→XをXのcosliceへ持ち上げる型。原文のC\_\{X/\}→Dの相対同値・評価のtrivial Kan性・π₀全単射とは別の対象と射。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex.exists_cosliceLift`

:::

:::corollary "kerodon_5_6_6_20" (uses := "kerodon_1_4_0_1, kerodon_4_7_3_9, kerodon_5_6_6_19")
Kerodon Corollary 5.6.6.20（[Tag 03J6](https://kerodon.net/tag/03J6)）。対応表の状態：一部。

QCatEquivalence.map\_isInitialVertexは原文のFが同値なら指定始対象の像も始対象となる方向を同じFについて直接返す。左ファイブレーションの仮定すら不要。逆は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.QCatEquivalence.map_isInitialVertex`

:::

:::proposition "kerodon_5_6_6_21" (uses := "kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_4_6_4_1, kerodon_4_7_3_20, kerodon_5_1_7_16, kerodon_5_2_8_1, kerodon_5_2_8_7, kerodon_5_2_8_12, kerodon_5_6_6_10, kerodon_5_6_6_19")
Kerodon Proposition 5.6.6.21（[Tag 02J8](https://kerodon.net/tag/02J8)）。対応表の状態：一部。

parametrizedFiberTransport\_evaluate\_isQCatEquivalence\_of\_initialVertexは原文(1)の始対象⇒同じパラメーター付き輸送を指定点で評価した射の同値、という方向を直接返す。逆・豊穣表現可能性の各iffは含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representableUnstraighteningIdentity_isInitialVertex`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.parametrizedFiberTransport_evaluate_isQCatEquivalence_of_initialVertex`

:::

# 5.6.7 Application: Extending Cocartesian Fibrations

%%%
number := false
tag := "kerodon-5-6-7"
%%%

Kerodon [Tag 029B](https://kerodon.net/tag/029B)

:::lemma_ "kerodon_5_6_7_1" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_4_4_4_9, kerodon_4_4_5_8, kerodon_5_1_7_9, kerodon_5_1_7_13")
Kerodon Lemma 5.6.7.1（[Tag 029C](https://kerodon.net/tag/029C)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：左ファイブレーション・アノダインの特例・指数化と底変換・ファイバーと宇宙の特例を照合。C の部分複体上の指定同型を延長する cocartesian fibration の四角。通常の底変換の pullback 同型は任意の部分複体からの延長ではない。

:::

:::proposition "kerodon_5_6_7_2" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_5_1_4_1, kerodon_5_1_7_14, kerodon_5_5_3_3, kerodon_5_6_0_2, kerodon_5_6_2_2, kerodon_5_6_7_1")
Kerodon Proposition 5.6.7.2（[Tag 029E](https://kerodon.net/tag/029E)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：左ファイブレーション・アノダインの特例・指数化と底変換・ファイバーと宇宙の特例を照合。部分複体上の cocartesian fibration とファイバーの条件を持つ引き戻しによる延長。指定した底上の分類の型では延長先を作らない。

:::

:::corollary "kerodon_5_6_7_3" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_1_3_3, kerodon_4_5_4_14, kerodon_5_1_4_1, kerodon_5_6_7_2")
Kerodon Corollary 5.6.7.3（[Tag 029F](https://kerodon.net/tag/029F)）。対応表の状態：なし。

引用は既に大きい底の上にあるleft fibrationの表現を延長する。原文は底と全空間のfibration自体をinner anodyneな底変更で拡張する存在であり、対象が異なる。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.exists_leftTransportRepresentation_extension_innerAnodyne`

:::

:::corollary "kerodon_5_6_7_5" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_5_1_4_1, kerodon_5_1_4_9, kerodon_5_6_7_3")
Kerodon Corollary 5.6.7.5（[Tag 029G](https://kerodon.net/tag/029G)）。対応表の状態：一部。

底を準圏に強めるとcocartesianFibration\_kanEquivalenceLiftingは同じUのequivalence liftingを直接与え、inner性と可逆辺の持ち上げというisofibration判定に一致する。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianFibration_kanEquivalenceLifting`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianFibration_kanInvertibleTargetLifting`

:::

:::corollary "kerodon_5_6_7_6" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_5_8_10, kerodon_5_1_4_1, kerodon_5_3_6_1, kerodon_5_6_7_3")
Kerodon Corollary 5.6.7.6（[Tag 029H](https://kerodon.net/tag/029H)）。対応表の状態：一部。

底の圏同値をinner anodyneに制限するとcocartesianFibration\_pullback\_innerAnodyne\_isPrecompositionEquivalenceは同じpullback projectionの圏同値性を直接返す。任意の圏同値への一般化は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianFibration_pullback_innerAnodyne_isPrecompositionEquivalence`

:::

:::corollary "kerodon_5_6_7_7" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_5_1_4_1, kerodon_5_1_5_16, kerodon_5_6_7_3, kerodon_5_6_7_6")
Kerodon Corollary 5.6.7.7（[Tag 03TX](https://kerodon.net/tag/03TX)）。対応表の状態：なし。

HasSmallSimplexFibers.essentiallySmallは宇宙版の頂点fiberの小ささ。原文の数値κとcf(κ)、全空間のessentiallyκ-smallとのiffのいずれの方向も直接返さない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.HasSmallSimplexFibers.essentiallySmall`

:::

:::corollary "kerodon_5_6_7_8"
Kerodon Corollary 5.6.7.8（[Tag 029K](https://kerodon.net/tag/029K)）。対応表の状態：一部。

底を準圏、U,Vをleft fibrationに強めれば、圏同値Fを前合成同値へ移しexists\_relativeFunctorInverse\_of\_precompositionEquivalenceで同じFの底上の相対逆と相対単位・余単位を直接得る。一般cocartesian版と逆は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.exists_relativeFunctorInverse_of_precompositionEquivalence`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isPrecompositionEquivalence_iff_isQCatEquivalence`

:::

# 5.6.8 Transport Witnesses

%%%
number := false
tag := "kerodon-5-6-8"
%%%

Kerodon [Tag 02S9](https://kerodon.net/tag/02S9)

:::definition "kerodon_5_6_8_1"
Kerodon Notation 5.6.8.1（[Tag 02SA](https://kerodon.net/tag/02SA)）。対応表の状態：なし。

transportWitnessSpaceは空間値のleft transportの証人全体。原文TWはQC値表現の証人全体であり、Uがleft fibrationでも任意QC値表現を空間値データに同定する比較なしには同じ部分単体集合にならない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessSpace`

:::

:::theorem "kerodon_5_6_8_3" (uses := "kerodon_1_1_0_6, kerodon_1_1_4_12, kerodon_1_2_5_1, kerodon_3_2_7_2, kerodon_5_1_4_1, kerodon_5_6_8_10, kerodon_5_6_9_1, kerodon_5_6_9_2")
Kerodon Theorem 5.6.8.3（[Tag 02SC](https://kerodon.net/tag/02SC)）。対応表の状態：なし。

可縮性の型は空間値のtransportWitnessSpace。原文のQC値表現全体のTWとの比較がないので、left fibrationに制限しても同じTWの可縮性とは言えない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallTransportWitnessSpace_isContractibleKan`

:::

:::lemma_ "kerodon_5_6_8_5" (uses := "kerodon_1_1_0_6, kerodon_1_5_4_13, kerodon_5_1_1_1, kerodon_5_1_4_1, kerodon_5_1_4_13")
Kerodon Lemma 5.6.8.5（[Tag 02SE](https://kerodon.net/tag/02SE)）。対応表の状態：なし。

引用のIsRepresentationは空間値left transportのfiber同値条件。原文のQC\_Objによる指定四角が表現になる条件との同定がない。頂点全射での検出は類似の判定。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SquareRepresentationRestriction.LeftTransportSquare.isRepresentation_iff_restrict_of_vertexSurjective`

:::

:::lemma_ "kerodon_5_6_8_6" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_1_5_3_7, kerodon_1_5_7_5, kerodon_4_1_4_3, kerodon_5_1_1_1, kerodon_5_1_1_9, kerodon_5_1_2_4, kerodon_5_1_4_1, kerodon_5_6_8_5")
Kerodon Lemma 5.6.8.6（[Tag 02SF](https://kerodon.net/tag/02SF)）。対応表の状態：なし。

引用は空間値LeftTransportSquareの表現条件を可逆辺に沿って保つ。原文のQC値の全四角のMとそのreplete部分TWは別の対象で、同定する比較がない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftTransportSquare.isRepresentation_of_edge`

:::

:::lemma_ "kerodon_5_6_8_7" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_4_4_2_1, kerodon_4_4_3_19, kerodon_4_4_4_4, kerodon_5_1_1_1, kerodon_5_1_1_11, kerodon_5_1_4_1, kerodon_5_2_5_2, kerodon_5_6_8_6")
Kerodon Lemma 5.6.8.7（[Tag 02SG](https://kerodon.net/tag/02SG)）。対応表の状態：なし。

Kan性の型は空間値left transportの証人空間。原文のQC値の全表現のTWとの比較を欠くため、同じ対象の特殊形の結論ではない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessSpace_kanComplex`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessEdge_isInvertible`

:::

:::definition "kerodon_5_6_8_9" (uses := "kerodon_1_1_0_6, kerodon_5_1_4_1")
Kerodon Notation 5.6.8.9（[Tag 02SJ](https://kerodon.net/tag/02SJ)）。対応表の状態：なし。

引用の制限写像は空間値TW間。原文のQC値TWの指定制限射との比較がなく、余極限から極限への保存の主張も含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessRestriction`

:::

:::lemma_ "kerodon_5_6_8_10" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_1_5_7_6, kerodon_4_4_5_1, kerodon_4_4_5_3, kerodon_4_5_6_18, kerodon_5_1_4_1, kerodon_5_3_6_6, kerodon_5_6_8_5, kerodon_5_6_8_6, kerodon_5_6_8_7, kerodon_5_6_8_9")
Kerodon Lemma 5.6.8.10（[Tag 02SK](https://kerodon.net/tag/02SK)）。対応表の状態：なし。

引用のfibration性とinner anodyneでのtrivial性は空間値TWの制限。原文のQC値のTWの制限と同じ射である比較がない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportRepresentationInnerExtension_isContractibleKan`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessRestriction_trivialKanFibration_of_innerAnodyne`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.WitnessRestrictionFibration.transportWitnessRestriction_fibration`

:::

# 5.6.9 Proof of the Universality Theorem

%%%
number := false
tag := "kerodon-5-6-9"
%%%

Kerodon [Tag 02SM](https://kerodon.net/tag/02SM)

:::lemma_ "kerodon_5_6_9_1" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_3_2_7_2, kerodon_3_2_8_1, kerodon_3_3_7_6, kerodon_3_4_1_5, kerodon_3_4_1_11, kerodon_4_4_3_7, kerodon_4_4_5_1, kerodon_4_4_5_7, kerodon_5_1_1_1, kerodon_5_1_4_1, kerodon_5_2_1_1, kerodon_5_2_1_3, kerodon_5_2_2_4, kerodon_5_2_2_8, kerodon_5_2_4_2, kerodon_5_2_8_1, kerodon_5_5_5_14, kerodon_5_6_8_10")
Kerodon Lemma 5.6.9.1（[Tag 02SN](https://kerodon.net/tag/02SN)）。対応表の状態：なし。

引用は一点上の空間値証人空間を関手空間として区間境界へ制限する射。原文のΔ¹上の一般cocartesian fibrationのQC値TWの制限への同定がない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointWitnessIntervalBoundary_trivialKanFibration`

:::

:::lemma_ "kerodon_5_6_9_2" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_3_5_1_33, kerodon_5_6_8_7, kerodon_5_6_9_1")
Kerodon Lemma 5.6.9.2（[Tag 02SR](https://kerodon.net/tag/02SR)）。対応表の状態：なし。

引用は一点上のleft fibrationの空間値証人空間。原文の任意の準圏EのQC値TWと比較する型がなく、EがKanという制限だけでは同じ証人空間にならない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointTransportWitnessSpace_isContractibleKan`

:::

