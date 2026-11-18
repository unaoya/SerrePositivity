import Verso
import VersoManual
import VersoBlueprint
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.EssentialImage
import Mathlib.CategoryTheory.Quotient
import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.Equivalence
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithful
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FunctorEdgePointwise
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.FullSubcomplexFibration
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.EquivalenceTerminal
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TerminalVertices

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "4.8 Full, Faithful, and Essentially Surjective Functors" =>
%%%
number := false
tag := "kerodon-4-8"
%%%

Kerodon の 4.8 節（[Tag 0578](https://kerodon.net/tag/0578)）の項目と、SerrePositivity・Mathlib の宣言との対応。本文は対応表（research/kerodon-coverage）の判定の理由の要約で、Kerodon の本文の写しではない。

:::theorem "kerodon_4_8_0_1" (lean := "CategoryTheory.Functor.IsEquivalence, CategoryTheory.Functor.essImage")
Kerodon Theorem 4.8.0.1（[Tag 06RY](https://kerodon.net/tag/06RY)）。対応表の状態：Mathlib にある。

仮定：通常の圏 C,D と関手 F（Kerodon と一致）。結論：Functor.IsEquivalence は Full・Faithful・EssSurj を束ね、その関手から圏同値を作る（一致）。

:::

:::definition "kerodon_4_8_0_4"
Kerodon Definition 4.8.0.4（[Tag 057B](https://kerodon.net/tag/057B)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：通常圏の full・境界持ち上げの全次数を照合。isofibration に対する次数 n の境界持ち上げによる n-full。EquivalenceLifting の試験射は前合成同値な単射。

:::

# 4.8.1 Essentially Surjective Functors

%%%
number := false
tag := "kerodon-4-8-1"
%%%

Kerodon [Tag 01JG](https://kerodon.net/tag/01JG)

:::definition "kerodon_4_8_1_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsEssentiallySurjective")
Kerodon Definition 4.8.1.1（[Tag 01JQ](https://kerodon.net/tag/01JQ)）。対応表の状態：本体にある。

仮定：∞ 圏間の関手 F（Lean が弱い：述語は任意の単体集合の射）。結論：任意の標的頂点 y がある F(x) と hY で同型であること（一致）。

:::

:::proposition "kerodon_4_8_1_3" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.isEssentiallySurjective_iff_hoFunctor")
Kerodon Remark 4.8.1.3（[Tag 01JS](https://kerodon.net/tag/01JS)）。対応表の状態：本体にある。

仮定：∞ 圏間の関手 F（Lean が弱い：任意の単体集合の射）。結論：IsEssentiallySurjective F と誘導された hF の Functor.EssSurj が同値（一致）。

:::

:::proposition "kerodon_4_8_1_7" (uses := "kerodon_1_4_0_1")
Kerodon Remark 4.8.1.7（[Tag 01JW](https://kerodon.net/tag/01JW)）。対応表の状態：一部。

IsEssentiallySurjective.compは原文の三つの結論のうち、本質的全射な二関手の合成も本質的全射という第一成分を同じ合成について直接返す。後二条件は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsEssentiallySurjective.comp`

:::

:::definition "kerodon_4_8_1_11" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices, CategoryTheory.Functor.essImage, SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.fullSubcomplexOnVertices_quasicategory") (uses := "kerodon_1_4_0_1")
Kerodon Definition 4.8.1.11（[Tag 06S2](https://kerodon.net/tag/06S2)）。対応表の状態：本体にある。

fullSubcomplexOnVerticesにP(y):=∃x,Nonempty(VertexIso(F(x),y))を代入すると、原文と同じ「像の対象に同型な全頂点で張る充満部分圏」を直接構成する。VertexIsoが対象の同型を表し、fullSubcomplexOnVertices\_quasicategoryも現本体にある。専用のessImageという名前の欠如だけではpartialにしない。

:::

# 4.8.2 Full Functors

%%%
number := false
tag := "kerodon-4-8-2"
%%%

Kerodon [Tag 059U](https://kerodon.net/tag/059U)

:::definition "kerodon_4_8_2_1" (uses := "kerodon_1_4_0_1")
Kerodon Definition 4.8.2.1（[Tag 059V](https://kerodon.net/tag/059V)）。対応表の状態：なし。

Fullは通常圏のHom集合の全射性。原文のnerveの区間写像空間のπ₀との比較を引用型に含まず、単なる類似の定義だけは数えない。

宣言：`CategoryTheory.Functor.Full`

:::

:::definition "kerodon_4_8_2_7" (uses := "kerodon_1_4_0_1, kerodon_4_8_1_1, kerodon_4_8_2_1")
Kerodon Definition 4.8.2.7（[Tag 05A5](https://kerodon.net/tag/05A5)）。対応表の状態：一部。

IsEssentiallySurjectiveは原文の0-fullの定義の頂点同型による存在条件そのもの。1-fullと高次n-fullの定義は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsEssentiallySurjective`

:::

:::proposition "kerodon_4_8_2_20" (uses := "kerodon_1_2_5_1, kerodon_4_8_2_7")
Kerodon Proposition 4.8.2.20（[Tag 05AF](https://kerodon.net/tag/05AF)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：通常圏の full と合成・全次数の境界とファイバー・Kan の π₀・πₙを照合。Kan 複体の n-full と π₀ 又は πₙ の全射性の判定。ホモトピー群への誘導射にはこの n-full との同値がない。

:::

:::corollary "kerodon_4_8_2_22" (uses := "kerodon_1_4_0_1")
Kerodon Corollary 4.8.2.22（[Tag 05AH](https://kerodon.net/tag/05AH)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：通常圏の full と合成・全次数の境界とファイバー・Kan の π₀・πₙを照合。n≥1 の n-full 性と対象対ごとの Hom 射の次数を一つ下げた full 性。pinched Hom の同値は任意次数の判定ではない。

:::

:::corollary "kerodon_4_8_2_24" (uses := "kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_4_6_1_22, kerodon_4_8_2_22")
Kerodon Corollary 4.8.2.24（[Tag 05AL](https://kerodon.net/tag/05AL)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：通常圏の full と合成・全次数の境界とファイバー・Kan の π₀・πₙを照合。内ファイブレーションの n-full と各像射の上の持ち上げ空間の連結度の同値。頂点上ファイバーの計算は射 u を固定しない。

:::

:::proposition "kerodon_4_8_2_25" (uses := "kerodon_1_4_0_1, kerodon_4_8_2_24")
Kerodon Proposition 4.8.2.25（[Tag 05AN](https://kerodon.net/tag/05AN)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：通常圏の full と合成・全次数の境界とファイバー・Kan の π₀・πₙを照合。n-full 性を各ファイバーで判定する条件と基底変換の条件の同値。pullback の内ファイブレーション性だけでは判定を与えない。

:::

:::corollary "kerodon_4_8_2_26"
Kerodon Corollary 4.8.2.26（[Tag 05J2](https://kerodon.net/tag/05J2)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：通常圏の full と合成・全次数の境界とファイバー・Kan の π₀・πₙを照合。内ファイブレーション間の四角で、指定ファイバーの写像空間の条件から n-full 性を移す結論。単なる基底変換の型では対象が違う。

:::

:::corollary "kerodon_4_8_2_27"
Kerodon Corollary 4.8.2.27（[Tag 05AP](https://kerodon.net/tag/05AP)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：通常圏の full と合成・全次数の境界とファイバー・Kan の π₀・πₙを照合。categorical pullback による n-full の保存。通常圏の Full.pullback や厳密 pullback の ∞ 圏性では任意 n を扱わない。

:::

:::proposition "kerodon_4_8_2_28" (uses := "kerodon_1_4_0_1, kerodon_4_8_2_25")
Kerodon Proposition 4.8.2.28（[Tag 05AS](https://kerodon.net/tag/05AS)）。対応表の状態：なし。

Full.of\_comp\_faithfulは通常圏のFull/Faithfulの消去。原文のnerveの写像空間でのn-fullの条件への比較がなく、類似の通常圏命題だけでは数えない。

宣言：`CategoryTheory.Functor.Full.of_comp_faithful`

:::

:::proposition "kerodon_4_8_2_30" (uses := "kerodon_1_4_0_1, kerodon_4_8_2_25")
Kerodon Proposition 4.8.2.30（[Tag 05AU](https://kerodon.net/tag/05AU)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：通常圏の full と合成・全次数の境界とファイバー・Kan の π₀・πₙを照合。前段の本質的全射性・full 性・(n−1)-full 性から合成の n-full 性を後段に移す結論。通常の full 合成は仮定も次数も異なる。

:::

# 4.8.3 Faithful Functors

%%%
number := false
tag := "kerodon-4-8-3"
%%%

Kerodon [Tag 05AW](https://kerodon.net/tag/05AW)

:::definition "kerodon_4_8_3_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful")
Kerodon Definition 4.8.3.1（[Tag 01JH](https://kerodon.net/tag/01JH)）。対応表の状態：本体にある。

仮定：∞ 圏間の関手 F（Lean が弱い：述語は任意の単体集合の射）。結論：任意の頂点対に対し右 pinched の写像空間の射が単体的ホモトピー同値。区間模型との比較を通した条件（一致）。

:::

:::proposition "kerodon_4_8_3_5" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful.reflects_isInvertibleEdge, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsFullyFaithful.reflects_isTerminalVertex")
Kerodon Proposition 4.8.3.5（[Tag 01JN](https://kerodon.net/tag/01JN)）。対応表の状態：本体にある。

仮定：Quasicategory X,Y と充満忠実な F、始域の辺 e（Kerodon と一致）。結論：F(e) の可逆性から e の可逆性を得る（一致）。

:::

:::proposition "kerodon_4_8_3_7" (uses := "kerodon_1_4_0_1, kerodon_4_6_1_22")
Kerodon Proposition 4.8.3.7（[Tag 05P5](https://kerodon.net/tag/05P5)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：通常圏の faithful・充満忠実な場合・対角とファイバーを照合。内ファイブレーションで strict pullback を homotopy pullback に入れる包含の充満忠実性。strict pullback の射影に対する候補は比較射を変えている。

:::

:::definition "kerodon_4_8_3_8" (uses := "kerodon_1_4_0_1")
Kerodon Definition 4.8.3.8（[Tag 059W](https://kerodon.net/tag/059W)）。対応表の状態：なし。

Faithfulは通常圏のHom集合の単射性。原文の写像空間の直和因子への同値との比較を欠く。

宣言：`CategoryTheory.Functor.Faithful`

:::

:::proposition "kerodon_4_8_3_9" (uses := "kerodon_1_4_0_1, kerodon_4_8_2_1, kerodon_4_8_3_1, kerodon_4_8_3_8")
Kerodon Remark 4.8.3.9（[Tag 059X](https://kerodon.net/tag/059X)）。対応表の状態：一部。

IsFullyFaithfulの各pinchedHomMapのホモトピー同値は、自然なpinched→interval比較の同値と可換式で同じinterval作用の同値へ移る。従ってπ₀全射と全標的を直和因子とする同値を直接得る。fully faithful⇒fullかつfaithfulの向きのみ。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful.toHoFullyFaithful`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsFullyFaithful.comp`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace_isQCatEquivalence`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace_postOfEq`

:::

:::definition "kerodon_4_8_3_12"
Kerodon Definition 4.8.3.12（[Tag 05AX](https://kerodon.net/tag/05AX)）。対応表の状態：一部。

n=0の(n−2)-truncationは各Hom作用のホモトピー同値の条件。IsFullyFaithfulのpinchedHomMapを自然な区間比較で移すと同じinterval作用のこの条件を直接得る。任意の正のnの定義は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace_isQCatEquivalence`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace_postOfEq`

:::

:::definition "kerodon_4_8_3_15"
Kerodon Variant 4.8.3.15（[Tag 06SD](https://kerodon.net/tag/06SD)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：通常圏の faithful・充満忠実な場合・対角とファイバーを照合。負次数に拡張した n-faithful の規約。fully faithful の宣言は負次数を含む族ではない。

:::

:::definition "kerodon_4_8_3_32" (uses := "kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_3_5_9_11, kerodon_4_6_1_22")
Kerodon Variant 4.8.3.32（[Tag 06SN](https://kerodon.net/tag/06SN)）。対応表の状態：なし。

pinchedHomPullbackBaseMapは一つの比較射、追加の充満忠実性下での帰結もpinched模型。自然な区間比較の圏同値だけでは厳密pullback性やfibration性は移らず、原文の指定四角の比較が必要。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomPullbackBaseMap`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful.pinchedHomMap_pullback_snd_trivialKanFibration`

:::

:::definition "kerodon_4_8_3_35"
Kerodon Variant 4.8.3.35（[Tag 05BB](https://kerodon.net/tag/05BB)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：通常圏の faithful・充満忠実な場合・対角とファイバーを照合。n-faithful と対角の n に依存する条件の同値。fully faithful の境界持ち上げの型は対角と次数の関係を述べない。

:::

:::proposition "kerodon_4_8_3_36"
Kerodon Proposition 4.8.3.36（[Tag 05BD](https://kerodon.net/tag/05BD)）。対応表の状態：一部。

n=0でIsFullyFaithful.pullback\_sndは同じinner fibrationの各底変換の充満忠実性を直接返す。pinched/interval比較は自然な同値なのでこの性質は原文の同じHom作用へ移る。一般nの四条件は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful.pullback_snd`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace_isQCatEquivalence`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace_postOfEq`

:::

:::definition "kerodon_4_8_3_38" (uses := "kerodon_1_4_0_1")
Kerodon Variant 4.8.3.38（[Tag 05J3](https://kerodon.net/tag/05J3)）。対応表の状態：なし。

区間上の端点fiberとcrossingの条件からの充満忠実性は、原文の全ての辺uへの引き戻しの同値条件とは異なる判定。h0/h1/hcを原文の仮定から回収する比較が要る。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.isFullyFaithful_over_interval_of_endpoint_fibers_of_crossing`

:::

:::corollary "kerodon_4_8_3_39" (uses := "kerodon_1_4_0_1, kerodon_4_8_3_32, kerodon_4_8_3_38")
Kerodon Corollary 4.8.3.39（[Tag 06SP](https://kerodon.net/tag/06SP)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：通常圏の faithful・充満忠実な場合・対角とファイバーを照合。内ファイブレーションの四角でファイバー側の条件から n-faithful 性を移す結論。四角の通常の忠実性や厳密 pullback の型ではない。

:::

# 4.8.4 Detecting Equivalences of ∞-Categories

%%%
number := false
tag := "kerodon-4-8-4"
%%%

Kerodon [Tag 06SQ](https://kerodon.net/tag/06SQ)

:::theorem "kerodon_4_8_4_1" (uses := "kerodon_1_4_0_1, kerodon_4_5_3_24, kerodon_4_5_4_11, kerodon_4_8_3_9, kerodon_4_8_4_5")
Kerodon Theorem 4.8.4.1（[Tag 01JX](https://kerodon.net/tag/01JX)）。対応表の状態：一部。

isQCatEquivalence\_iff\_fullyFaithful\_essentiallySurjectiveは同じFの原文(1)⇔(2)を直接返す。pinchedとintervalの自然な比較によるHom作用の同値性も確認する。(3),(4)を含む四条件全体ではない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isQCatEquivalence_iff_fullyFaithful_essentiallySurjective`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.qCatEquivalenceOfFullyFaithfulEssentiallySurjective`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful.isQCatEquivalence_of_surjective`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace_isQCatEquivalence`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace_postOfEq`

:::

:::corollary "kerodon_4_8_4_4" (uses := "kerodon_1_4_0_1, kerodon_4_8_1_11")
Kerodon Corollary 4.8.4.4（[Tag 01K0](https://kerodon.net/tag/01K0)）。対応表の状態：なし。

fullSubcomplexVertexImageLiftは頂点のliteral imageが張る部分複体への射。原文の同型で閉じたessential imageとは対象が異なり、この射が同値という型だけでは同じ結論にならない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.fullSubcomplexVertexImageLift_isQCatEquivalence`

:::

:::proposition "kerodon_4_8_4_5" (uses := "kerodon_1_4_0_1, kerodon_4_7_6_25, kerodon_4_8_2_24, kerodon_4_8_2_25")
Kerodon Proposition 4.8.4.5（[Tag 05AR](https://kerodon.net/tag/05AR)）。対応表の状態：一部。

IsFullyFaithful.hasLiftingProperty\_boundary\_succはFを充満忠実なinner fibrationに強めると同じ∂Δⁿに対する持ち上げを全ての正のnで直接返す。一つのn-fullだけの仮定と逆向きは含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful.hasLiftingProperty_boundary_succ`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.isFullyFaithful_of_boundary_succ`

:::

:::theorem "kerodon_4_8_4_6" (uses := "kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_3_2_8_3, kerodon_3_3_7_1, kerodon_4_4_5_4, kerodon_4_5_1_22, kerodon_4_8_4_1")
Kerodon Theorem 4.8.4.6（[Tag 01HG](https://kerodon.net/tag/01HG)）。対応表の状態：一部。

Fの圏同値からpostcomposeをΔ¹に適用し、IsQCatEquivalence.coreとKan上のホモトピー同値への比較を適用すると、原文の同じ矢印関手圏coreの射のホモトピー同値性を直接得る。逆向きは含まない。

宣言：`SerrePositivity.InfinityCategories.HTT.Section3_1_3.IsQCatEquivalence.core`

:::

:::corollary "kerodon_4_8_4_7"
Kerodon Corollary 4.8.4.7（[Tag 034V](https://kerodon.net/tag/034V)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：完全忠実な場合・通常圏の full/faithful・相対関手圏・引き戻しを照合。categorical pullback の四角から原文で指定した比較四角を構成する判定。pinched Hom pullback のみではその比較の全ての条件を与えない。

:::

:::definition "kerodon_4_8_4_8" (uses := "kerodon_1_1_0_6")
Kerodon Definition 4.8.4.8（[Tag 01Q0](https://kerodon.net/tag/01Q0)）。対応表の状態：一部。

coherentNerveMap\_isFullyFaithful\_iffの右辺は局所Kanな豊穣圏で全てのF.map X Yが圏同値という条件で、Kan上の弱ホモトピー同値との比較により原文のweakly fully faithfulの条件を直接与える。この範囲と前半の条件のみで、weakly essentially surjectiveと一般のweak equivalenceの定義は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.coherentNerveMap_isFullyFaithful_iff`

:::

:::corollary "kerodon_4_8_4_9"
Kerodon Corollary 4.8.4.9（[Tag 01Q1](https://kerodon.net/tag/01Q1)）。対応表の状態：なし。

引用は包含順coherent nerveの右pinchedの判定。原文の逆包含Pathによるcoherent nerveと特定の比較射との同定がなく、原文の同じN\^hc(F)の三つのiffとして直接適用できない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.coherentNerveMap_isFullyFaithful_iff`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.coherentNerveMap_pinchedHomMap_isQCatEquivalence_iff`

:::

:::proposition "kerodon_4_8_4_10"
Kerodon Proposition 4.8.4.10（[Tag 058M](https://kerodon.net/tag/058M)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：完全忠実な場合・通常圏の full/faithful・相対関手圏・引き戻しを照合。局所 n-truncation を表示することと各 Hom の n-truncation の条件の同値。fully faithful の Hom 同値は切断の普遍性と異なる。

:::

:::proposition "kerodon_4_8_4_11"
Kerodon Proposition 4.8.4.11（[Tag 05A2](https://kerodon.net/tag/05A2)）。対応表の状態：なし。

Faithfulは通常圏のHom集合上の述語。原文の∞圏のfaithful性とhFのfaithful性・指定categorical pullbackの二条件を結ぶ型ではない。

宣言：`CategoryTheory.Functor.Faithful`

:::

:::proposition "kerodon_4_8_4_13" (uses := "kerodon_1_1_0_6, kerodon_1_1_4_12, kerodon_1_4_0_1, kerodon_4_8_4_5")
Kerodon Proposition 4.8.4.13（[Tag 05BF](https://kerodon.net/tag/05BF)）。対応表の状態：一部。

n=0では充満忠実性と全ての正次元境界のRLPを、hasLiftingProperty\_boundary\_succとisFullyFaithful\_of\_boundary\_succが同じFについて直接結ぶ。自然なpinched/interval比較でHom作用を同定できる。一般nと全てのA⊂Bの条件(3)は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful.hasLiftingProperty_boundary_succ`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.isFullyFaithful_of_boundary_succ`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful.trivialKanFibration_of_surjective`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace_isQCatEquivalence`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace_postOfEq`

:::

:::corollary "kerodon_4_8_4_14"
Kerodon Corollary 4.8.4.14（[Tag 05BG](https://kerodon.net/tag/05BG)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：完全忠実な場合・通常圏の full/faithful・相対関手圏・引き戻しを照合。n-faithful な射から A⊂B に沿う相対的関手圏射の n-faithful 性。ihom の内ファイブレーション性には次数付き忠実性がない。

:::

:::corollary "kerodon_4_8_4_15"
Kerodon Corollary 4.8.4.15（[Tag 04Q6](https://kerodon.net/tag/04Q6)）。対応表の状態：一部。

IsFullyFaithful.postcomposeは原文が明記する「特に充満忠実なら内部Homの同じ後合成も充満忠実」を直接返す。写像空間模型の自然な比較を通じる性質で、一般n-faithfulは含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful.postcompose`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace_isQCatEquivalence`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace_postOfEq`

:::

:::corollary "kerodon_4_8_4_16"
Kerodon Corollary 4.8.4.16（[Tag 05BK](https://kerodon.net/tag/05BK)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：完全忠実な場合・通常圏の full/faithful・相対関手圏・引き戻しを照合。n-faithful な F の上の Fun\_\{/D\}(B,C) の局所 (n−2)-truncation。相対関手圏の ∞ 圏性からは指定次数を得ない。

:::

:::corollary "kerodon_4_8_4_17" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_3_1_8_1, kerodon_4_3_6_10, kerodon_4_6_4_21, kerodon_4_8_4_1, kerodon_4_8_4_13")
Kerodon Corollary 4.8.4.17（[Tag 02C8](https://kerodon.net/tag/02C8)）。対応表の状態：一部。

fullSubcomplex\_coslicePostcomp\_isFullyFaithfulはGが同型で閉じた頂点集合の充満部分複体の包含の場合の同じcoslice後合成の充満忠実性。一般G・slice側・一般nは含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.fullSubcomplex_coslicePostcomp_isFullyFaithful`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace_isQCatEquivalence`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace_postOfEq`

:::

# 4.8.5 Categorically Connective Functors

%%%
number := false
tag := "kerodon-4-8-5"
%%%

Kerodon [Tag 05BY](https://kerodon.net/tag/05BY)

:::definition "kerodon_4_8_5_1"
Kerodon Definition 4.8.5.1（[Tag 05BZ](https://kerodon.net/tag/05BZ)）。対応表の状態：一部。

IsEssentiallySurjectiveはn=0で唯一要求される0-fullの条件をそのまま与える。他のnでの全てのm-fullの条件は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsEssentiallySurjective`

:::

:::proposition "kerodon_4_8_5_15"
Kerodon Proposition 4.8.5.15（[Tag 05CA](https://kerodon.net/tag/05CA)）。対応表の状態：一部。

n=0ではcategorically 0-connectiveは0-fullすなわち本質的全射だけ。IsEssentiallySurjective.compは同じF,Gの合成についてこの結論を直接返す。(1)のn=0の場合に限り、一般nや(2),(3)は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsEssentiallySurjective.comp`

:::

:::proposition "kerodon_4_8_5_17"
Kerodon Proposition 4.8.5.17（[Tag 05CC](https://kerodon.net/tag/05CC)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n を固定する等価の場合・空間版の連結・次元・持ち上げを照合。isofibration の圏的 n-connectivity と dim≤n の包含に対する持ち上げの同値。一般の同値持ち上げは全ての低次元包含を試験しない。

:::

:::proposition "kerodon_4_8_5_18"
Kerodon Proposition 4.8.5.18（[Tag 05CB](https://kerodon.net/tag/05CB)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n を固定する等価の場合・空間版の連結・次元・持ち上げを照合。n 未満で全単射・n で全射となる F の圏的 n-connectivity。単体レベルの全射条件だけを扱う型では結論が違う。

:::

:::proposition "kerodon_4_8_5_20"
Kerodon Proposition 4.8.5.20（[Tag 05CD](https://kerodon.net/tag/05CD)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n を固定する等価の場合・空間版の連結・次元・持ち上げを照合。isofibration の圏的 n-connectivity と単体次数で全単射となる因子をもつ分解の同値。内アノダイン分解は n を指定しない。

:::

:::corollary "kerodon_4_8_5_21"
Kerodon Corollary 4.8.5.21（[Tag 05CF](https://kerodon.net/tag/05CF)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n を固定する等価の場合・空間版の連結・次元・持ち上げを照合。圏的 n-connective な ∞ 圏射の dim≤n の因子を伴う分解とその逆。通常の horn small-object factorization には次元の上限がない。

:::

:::corollary "kerodon_4_8_5_22"
Kerodon Corollary 4.8.5.22（[Tag 05CG](https://kerodon.net/tag/05CG)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n を固定する等価の場合・空間版の連結・次元・持ち上げを照合。圏的 n-connectivity が空間的 n-connectivity を含意する比較。piConnective の定義は後者側だけで前者との含意を述べない。

:::

:::corollary "kerodon_4_8_5_23"
Kerodon Corollary 4.8.5.23（[Tag 05CH](https://kerodon.net/tag/05CH)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n を固定する等価の場合・空間版の連結・次元・持ち上げを照合。圏的 n-connective と n-faithful の直交性。Mathlib の HasLiftingProperty だけでは指定二クラスの直交性を得ない。

:::

:::proposition "kerodon_4_8_5_25"
Kerodon Proposition 4.8.5.25（[Tag 05CL](https://kerodon.net/tag/05CL)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n を固定する等価の場合・空間版の連結・次元・持ち上げを照合。dim B≤m で圏的 (m+n)-connective 射が Fun(B,−) 上誘導する次数 n の結論。指数対象のファイブレーション性は次数を評価しない。

:::

:::corollary "kerodon_4_8_5_26"
Kerodon Corollary 4.8.5.26（[Tag 05CN](https://kerodon.net/tag/05CN)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n を固定する等価の場合・空間版の連結・次元・持ち上げを照合。dim B≤m で圏的 (m+n)-connective な F が誘導する相対 Fun 比較の次数 n。絶対 Fun の前合成同値はこの相対比較と異なる。

:::

# 4.8.6 Digression: \$n\$-Categorical Fibrations

%%%
number := false
tag := "kerodon-4-8-6"
%%%

Kerodon [Tag 06SY](https://kerodon.net/tag/06SY)

:::definition "kerodon_4_8_6_1"
Kerodon Definition 4.8.6.1（[Tag 05BL](https://kerodon.net/tag/05BL)）。対応表の状態：一部。

始域・標的を薄い通常圏のnerveとしn=1に取ると、thinNerve\_innerFibrationが同じpの存在、thinNerve\_hom\_ext\_hornを始域に適用して次数2以上の一意性を直接得る。一般n・任意の始域は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.thinNerve_innerFibration`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.thinNerve_hom_ext_horn`

:::

:::definition "kerodon_4_8_6_2"
Kerodon Variant 4.8.6.2（[Tag 05BM](https://kerodon.net/tag/05BM)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n＝1 の nerve の内ホーンと相対 hC・n＝∞ の内ファイブレーション・左・右・Kan の特例を照合。0 次及び負次数の categorical inner fibration の各 Δᵐ 上のファイバーによる定義。内ファイブレーションの基底変換だけでは 0-category 条件がない。

:::

:::proposition "kerodon_4_8_6_9"
Kerodon Proposition 4.8.6.9（[Tag 05BU](https://kerodon.net/tag/05BU)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n＝1 の nerve の内ホーンと相対 hC・n＝∞ の内ファイブレーション・左・右・Kan の特例を照合。n-category の底を持つ内ファイブレーションの n-categorical 性と全空間の n-category 性の同値。Quasicategory の伝播に次数はない。

:::

:::corollary "kerodon_4_8_6_11"
Kerodon Corollary 4.8.6.11（[Tag 05BW](https://kerodon.net/tag/05BW)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n＝1 の nerve の内ホーンと相対 hC・n＝∞ の内ファイブレーション・左・右・Kan の特例を照合。n-categorical な G を仮定した F と G∘F の n-categorical 性の同値。内ファイブレーションの合成だけでは一意性を反映しない。

:::

:::proposition "kerodon_4_8_6_12"
Kerodon Proposition 4.8.6.12（[Tag 05BX](https://kerodon.net/tag/05BX)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n＝1 の nerve の内ホーンと相対 hC・n＝∞ の内ファイブレーション・左・右・Kan の特例を照合。n-categorical inner fibration の (n+1)-faithful 性。fully faithful の基底変換には n-categorical の仮定がない。

:::

:::definition "kerodon_4_8_6_13"
Kerodon Construction 4.8.6.13（[Tag 05CZ](https://kerodon.net/tag/05CZ)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n＝1 の nerve の内ホーンと相対 hC・n＝∞ の内ファイブレーション・左・右・Kan の特例を照合。各 Δᵐ 上の相対ファイバーから構成する h≤n(C/D)。絶対 HomotopyCategory の構成は D 上の単体ごとの比較を与えない。

:::

:::proposition "kerodon_4_8_6_17"
Kerodon Proposition 4.8.6.17（[Tag 05D3](https://kerodon.net/tag/05D3)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n＝1 の nerve の内ホーンと相対 hC・n＝∞ の内ファイブレーション・左・右・Kan の特例を照合。相対 h≤n(C/D)→D の n-categorical inner fibration 性。内ファイブレーションの射影型には相対商構成と n の一意性がない。

:::

:::corollary "kerodon_4_8_6_19"
Kerodon Corollary 4.8.6.19（[Tag 05D8](https://kerodon.net/tag/05D8)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n＝1 の nerve の内ホーンと相対 hC・n＝∞ の内ファイブレーション・左・右・Kan の特例を照合。任意 n における h≤n(C/D) と比較因子の ∞ 圏の性質。通常の pullback の ∞ 圏性には相対 h≤n がない。

:::

:::proposition "kerodon_4_8_6_20"
Kerodon Proposition 4.8.6.20（[Tag 05D5](https://kerodon.net/tag/05D5)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n＝1 の nerve の内ホーンと相対 hC・n＝∞ の内ファイブレーション・左・右・Kan の特例を照合。n-categorical な D′→D に対する相対 h≤n の指定 Fun 比較の性質。slice の通常の普遍性は対象の次数を制限しない。

:::

:::proposition "kerodon_4_8_6_22"
Kerodon Proposition 4.8.6.22（[Tag 05D7](https://kerodon.net/tag/05D7)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n＝1 の nerve の内ホーンと相対 hC・n＝∞ の内ファイブレーション・左・右・Kan の特例を照合。C→h≤n(C/D) 自身の内ファイブレーション性。一般の inner anodyne 分解は指定の比較射を扱わない。

:::

:::proposition "kerodon_4_8_6_23"
Kerodon Proposition 4.8.6.23（[Tag 05DA](https://kerodon.net/tag/05DA)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n＝1 の nerve の内ホーンと相対 hC・n＝∞ の内ファイブレーション・左・右・Kan の特例を照合。h≤n(C/D)→D の categorical/左/右/Kan ファイブレーション等の移行。op による左右反転は相対 h≤n の射に適用した型を与えない。

:::

:::proposition "kerodon_4_8_6_24"
Kerodon Proposition 4.8.6.24（[Tag 05DC](https://kerodon.net/tag/05DC)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n＝1 の nerve の内ホーンと相対 hC・n＝∞ の内ファイブレーション・左・右・Kan の特例を照合。内ファイブレーションの (n+1)-faithful 性と h≤n への比較の性質の同値。IsFullyFaithful の判定とは次数も比較も異なる。

:::

:::corollary "kerodon_4_8_6_25"
Kerodon Corollary 4.8.6.25（[Tag 05DD](https://kerodon.net/tag/05DD)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n＝1 の nerve の内ホーンと相対 hC・n＝∞ の内ファイブレーション・左・右・Kan の特例を照合。一般 F の (n+1)-faithful 性を n-categorical な因子で判定。通常圏の image 分解にはこの切断次数がない。

:::

:::proposition "kerodon_4_8_6_26"
Kerodon Proposition 4.8.6.26（[Tag 05DE](https://kerodon.net/tag/05DE)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n＝1 の nerve の内ホーンと相対 hC・n＝∞ の内ファイブレーション・左・右・Kan の特例を照合。categorical pullback と相対 h≤n の比較の両立。厳密 pullback の交換則だけでは h≤n を通した型がない。

:::

:::corollary "kerodon_4_8_6_27"
Kerodon Corollary 4.8.6.27（[Tag 05DF](https://kerodon.net/tag/05DF)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n＝1 の nerve の内ホーンと相対 hC・n＝∞ の内ファイブレーション・左・右・Kan の特例を照合。h≤n(C/D)→D の比較の性質と原文のファイバー条件の同値。単なるファイバー Kan 性は相対 h≤n の結論を含まない。

:::

# 4.8.7 Canonical Factorizations

%%%
number := false
tag := "kerodon-4-8-7"
%%%

Kerodon [Tag 05CP](https://kerodon.net/tag/05CP)

:::proposition "kerodon_4_8_7_1" (lean := "CategoryTheory.Functor.homRel, CategoryTheory.Quotient.functor, CategoryTheory.Quotient.full_functor, CategoryTheory.Quotient.essSurj_functor, CategoryTheory.Quotient.lift, CategoryTheory.Quotient.lift_spec")
Kerodon Proposition 4.8.7.1（[Tag 05CQ](https://kerodon.net/tag/05CQ)）。対応表の状態：Mathlib にある。

仮定：任意の通常圏 C,D と関手 F:C→D（Kerodon と一致）。結論：F.homRel で割る関手が Full かつ EssSurj。Quotient.lift が Faithful で、lift\_spec により合成は F（一致）。

:::

:::theorem "kerodon_4_8_7_3"
Kerodon Theorem 4.8.7.3（[Tag 05CS](https://kerodon.net/tag/05CS)）。対応表の状態：なし。

通常圏の商によるFull/EssSurj/Faithfulの分解で、原文のn-full/n-faithfulに関するnerve上の型と分解射の比較を欠く。

宣言：`CategoryTheory.Quotient.full_functor`、`CategoryTheory.Quotient.essSurj_functor`、`CategoryTheory.Quotient.lift_spec`

:::

:::corollary "kerodon_4_8_7_8"
Kerodon Corollary 4.8.7.8（[Tag 05CY](https://kerodon.net/tag/05CY)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：通常圏の商と因子分解・∞ 圏の本質像・切断・空間のモデル圏を照合。Kan 複体射を n-connective と (n−1)-truncated に分解。モデル圏の cofibration/fibration 分解のクラスは切断次数を指定しない。

:::

# 4.8.8 Categorically Connective Morphisms of Simplicial Sets

%%%
number := false
tag := "kerodon-4-8-8"
%%%

Kerodon [Tag 05DG](https://kerodon.net/tag/05DG)

:::proposition "kerodon_4_8_8_1"
Kerodon Proposition 4.8.8.1（[Tag 05DH](https://kerodon.net/tag/05DH)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：圏同値・内アノダインの特例・空間連結と次数・通常圏の直交と余極限を照合。圏的 n-connective 性を全ての n-faithful 射に対する Fun 比較で判定。前合成同値の定義は n-faithful の試験クラスを指定しない。

:::

:::definition "kerodon_4_8_8_2"
Kerodon Definition 4.8.8.2（[Tag 05DJ](https://kerodon.net/tag/05DJ)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：圏同値・内アノダインの特例・空間連結と次数・通常圏の直交と余極限を照合。任意の単体集合射への圏的 n-connective の拡張定義。境界集合に対する通常の llp には ∞ 圏間の n-faithful を試験する条件がない。

:::

:::proposition "kerodon_4_8_8_10" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_1_3_3")
Kerodon Proposition 4.8.8.10（[Tag 06T2](https://kerodon.net/tag/06T2)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：圏同値・内アノダインの特例・空間連結と次数・通常圏の直交と余極限を照合。圏的 n-connective 射で張る arrow 圏のフィルター余極限閉性。一般の射のクラスの余極限補題に当該クラスの同定がない。

:::

:::corollary "kerodon_4_8_8_11" (uses := "kerodon_1_1_0_6, kerodon_4_8_8_10")
Kerodon Corollary 4.8.8.11（[Tag 01HH](https://kerodon.net/tag/01HH)）。対応表の状態：なし。

引用の結論はt.app c.ptの前合成同値性。原文のArrow SSetでの余極限射との比較同型を直接述べず、ℕ列に限る場合にもF,Gの余極限比較の同定が必要。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_sequential_colimit`

:::

:::proposition "kerodon_4_8_8_12" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_5_3_19")
Kerodon Proposition 4.8.8.12（[Tag 05DP](https://kerodon.net/tag/05DP)）。対応表の状態：なし。

厳密pushoutでのIsPrecompositionEquivalence保存は、原文の指定次数nのn-full条件によるcategorical connectivityの結論ではない。その比較がなく、同じnの特殊形とは確認できない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence.of_isPushout`

:::

:::corollary "kerodon_4_8_8_13" (uses := "kerodon_1_1_0_6, kerodon_1_1_4_12, kerodon_4_5_5_11, kerodon_4_8_8_11, kerodon_4_8_8_12")
Kerodon Corollary 4.8.8.13（[Tag 06T3](https://kerodon.net/tag/06T3)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：圏同値・内アノダインの特例・空間連結と次数・通常圏の直交と余極限を照合。各 Δᵏ での基底変換上の圏的 n-connectivity から大域的圏的 n-connectivity。個別の pullback 型ではこの局所判定がない。

:::

:::corollary "kerodon_4_8_8_14" (uses := "kerodon_1_1_0_6, kerodon_4_8_8_13")
Kerodon Corollary 4.8.8.14（[Tag 023D](https://kerodon.net/tag/023D)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：圏同値・内アノダインの特例・空間連結と次数・通常圏の直交と余極限を照合。各 Δᵏ 上で categorical equivalence のときの大域比較。同値の基底変換の閉性では局所から大域への向きが逆。

:::

:::proposition "kerodon_4_8_8_15"
Kerodon Proposition 4.8.8.15（[Tag 05DR](https://kerodon.net/tag/05DR)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：圏同値・内アノダインの特例・空間連結と次数・通常圏の直交と余極限を照合。単射の圏的 n-connectivity と指定した持ち上げ条件の同値。anodyne の定義は次数と n-faithful の試験を持たない。

:::

:::proposition "kerodon_4_8_8_17"
Kerodon Proposition 4.8.8.17（[Tag 05DU](https://kerodon.net/tag/05DU)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：圏同値・内アノダインの特例・空間連結と次数・通常圏の直交と余極限を照合。任意の単体集合射で n 未満全単射・n で全射なら圏的 n-connective。通常の sk の単体ごとの同型の型に圏的結論がない。

:::

:::lemma_ "kerodon_4_8_8_18"
Kerodon Lemma 4.8.8.18（[Tag 06Y4](https://kerodon.net/tag/06Y4)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：圏同値・内アノダインの特例・空間連結と次数・通常圏の直交と余極限を照合。二つの単体境界の pushout-product 包含の圏的連結度の評価。一般の pushout-product の mono 性は n+m の評価を与えない。

:::

:::proposition "kerodon_4_8_8_19"
Kerodon Proposition 4.8.8.19（[Tag 06Y5](https://kerodon.net/tag/06Y5)）。対応表の状態：なし。

pushout-productの前合成同値性は全次数の圏同値に関する命題。原文の二つの有限連結度からm+n−1を得る結論やその同じ定義への比較を型に持たない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence.pushoutObjObj_right`

:::

:::proposition "kerodon_4_8_8_20"
Kerodon Proposition 4.8.8.20（[Tag 06Y6](https://kerodon.net/tag/06Y6)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：圏同値・内アノダインの特例・空間連結と次数・通常圏の直交と余極限を照合。n-faithful な U と圏的連結な f の相対 Fun 比較の結論。trivial Kan の指数随伴による移送の型には n-faithful がない。

:::

:::corollary "kerodon_4_8_8_21"
Kerodon Corollary 4.8.8.21（[Tag 06Y8](https://kerodon.net/tag/06Y8)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：圏同値・内アノダインの特例・空間連結と次数・通常圏の直交と余極限を照合。局所 (n−2)-truncated な C と圏的 m-connective な f の前合成の性質。precomposition equivalence の定義はこの二次数の条件を判定しない。

:::

