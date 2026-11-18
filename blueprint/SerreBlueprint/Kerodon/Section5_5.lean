import Verso
import VersoManual
import VersoBlueprint
import Mathlib.AlgebraicTopology.SimplicialNerve
import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.Vertices
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CoreKan
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PointedSpaceFiberVertices
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PointedSpaces
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCatSimplicial
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Slice

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "5.5 The ∞-Category QC" =>
%%%
number := false
tag := "kerodon-5-5"
%%%

Kerodon の 5.5 節（[Tag 01YV](https://kerodon.net/tag/01YV)）の項目と、SerrePositivity・Mathlib の宣言との対応。本文は対応表（research/kerodon-coverage）の判定の理由の要約で、Kerodon の本文の写しではない。

# 5.5.1 Digression: Slicing and the Homotopy Coherent Nerve

%%%
number := false
tag := "kerodon-5-5-1"
%%%

Kerodon [Tag 01Z5](https://kerodon.net/tag/01Z5)

:::definition "kerodon_5_5_1_1"
Kerodon Construction 5.5.1.1（[Tag 01Z6](https://kerodon.net/tag/01Z6)）。対応表の状態：なし。

Overは通常圏のsliceであり、原文の豊穣sliceのHomを単体集合の厳密fiberで作る構成への比較がない。通常圏の同名構成だけでは数えない。

宣言：`CategoryTheory.Over`

:::

:::definition "kerodon_5_5_1_3"
Kerodon Variant 5.5.1.3（[Tag 01Z8](https://kerodon.net/tag/01Z8)）。対応表の状態：なし。

Underは通常圏のcosliceであり、原文の豊穣cosliceの単体集合のHomの厳密fiberへの比較がない。

宣言：`CategoryTheory.Under`

:::

:::definition "kerodon_5_5_1_8"
Kerodon Notation 5.5.1.8（[Tag 01ZD](https://kerodon.net/tag/01ZD)）。対応表の状態：一部。

WithInitialは通常圏の場合に原文の対象集合Ob(C)⊔\{X₀\}を直接構成する。単体豊穣Homとその合成まで含む錐の全構成ではない。

宣言：`CategoryTheory.WithInitial`

:::

:::definition "kerodon_5_5_1_9"
Kerodon Variant 5.5.1.9（[Tag 01ZE](https://kerodon.net/tag/01ZE)）。対応表の状態：一部。

WithTerminalは通常圏の場合に原文の対象集合Ob(C)⊔\{Y₀\}を直接構成する。単体豊穣Homと合成は含まない。

宣言：`CategoryTheory.WithTerminal`

:::

:::definition "kerodon_5_5_1_15"
Kerodon Construction 5.5.1.15（[Tag 01ZL](https://kerodon.net/tag/01ZL)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の slice・錐・単体豊穣 slice と一点・局所 Kan・hc nerve の比較を照合。豊穣 slice/coslice の錐から C への指定 contraction functor。単体集合の join の評価は豊穣な関手ではない。

:::

:::proposition "kerodon_5_5_1_16"
Kerodon Proposition 5.5.1.16（[Tag 01ZM](https://kerodon.net/tag/01ZM)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の slice・錐・単体豊穣 slice と一点・局所 Kan・hc nerve の比較を照合。豊穣錐上の関手と指定頂点の豊穣 slice/coslice への関手の対応。通常の Over/Under の普遍性では enriched functor を量化しない。

:::

:::definition "kerodon_5_5_1_17"
Kerodon Construction 5.5.1.17（[Tag 01ZN](https://kerodon.net/tag/01ZN)）。対応表の状態：なし。

coherentCosliceFiberComparisonは一つの豊穣Homからcosliceのfiberへの射。原文は豊穣slice/cosliceのcoherent nerve全体からの比較関手であり、指定射への制限との比較が引用型にない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentCosliceFiberComparison`

:::

:::theorem "kerodon_5_5_1_21"
Kerodon Theorem 5.5.1.21（[Tag 01ZS](https://kerodon.net/tag/01ZS)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の slice・錐・単体豊穣 slice と一点・局所 Kan・hc nerve の比較を照合。豊穣 coslice の hc nerve 比較の圏同値性を合成 Hom の仮定から導く結論。単一の Kan ファイバーの比較は全 coslice の同値ではない。

:::

:::proposition "kerodon_5_5_1_22"
Kerodon Proposition 5.5.1.22（[Tag 01ZT](https://kerodon.net/tag/01ZT)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の slice・錐・単体豊穣 slice と一点・局所 Kan・hc nerve の比較を照合。豊穣 coslice の指定の充満部分圏への制限での比較の充満忠実性。coherent nerve の後合成の関手性からはこの仮定付き判定が出ない。

:::

# 5.5.2 The ∞-Category of Pointed Spaces

%%%
number := false
tag := "kerodon-5-5-2"
%%%

Kerodon [Tag 01ZV](https://kerodon.net/tag/01ZV)

:::definition "kerodon_5_5_2_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PointedSpaceInfinity, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceFiberVertexEquiv, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity")
Kerodon Construction 5.5.2.1（[Tag 01ZW](https://kerodon.net/tag/01ZW)）。対応表の状態：本体にある。

仮定：Kan 複体の coherent nerve と点 Δ⁰（Kerodon と一致）。結論：PointedSpaceInfinity は SpaceInfinity の Δ⁰ を表す頂点の下の coslice（一致）。

:::

:::proposition "kerodon_5_5_2_2" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceInfinity_quasicategory, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection_leftFibration")
Kerodon Proposition 5.5.2.2（[Tag 01ZX](https://kerodon.net/tag/01ZX)）。対応表の状態：本体にある。

仮定：点付き空間の coslice PointedSpaceInfinity とその射影（Kerodon と一致）。結論：PointedSpaceInfinity が Quasicategory、射影が LeftFibration（一致）。

:::

:::proposition "kerodon_5_5_2_6"
Kerodon Proposition 5.5.2.6（[Tag 02S2](https://kerodon.net/tag/02S2)）。対応表の状態：一部。

pointedSpaceFiberValueEquivalenceは各Sの頂点で、原文の輸送の値となるfiberとそのKan複体の同値を直接与える。豊穣関手の逆であるためのHom作用と自然性は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceFiberValueEquivalence`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceFiberVertexEquiv`

:::

:::proposition "kerodon_5_5_2_8"
Kerodon Proposition 5.5.2.8（[Tag 0200](https://kerodon.net/tag/0200)）。対応表の状態：なし。

coherentPointedFiberComparisonは各Kのfiberからの射。原文の全coslice比較関手の制限がこの射という比較がなく、その全関手の同値を直接結論しない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentPointedFiberComparison`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentPointedFiberComparison_isQCatEquivalence`

:::

:::corollary "kerodon_5_5_2_10"
Kerodon Corollary 5.5.2.10（[Tag 0202](https://kerodon.net/tag/0202)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：点付き Kan の hc nerve・各ファイバーの比較・通常群と nerveを照合。点付き Kan の hc nerve と S\_\* のホモトピー圏の同型。KST の pointedKanHomotopyClass\_comparison は指定辺の同値関係を比較するが両圏の比較同型を構成しない。

:::

:::proposition "kerodon_5_5_2_13"
Kerodon Proposition 5.5.2.13（[Tag 0205](https://kerodon.net/tag/0205)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：点付き Kan の hc nerve・各ファイバーの比較・通常群と nerveを照合。G↦BG の N(Group)→S\_\* の充満忠実性。KST の群の nerve の座標計算と通常 nerve の充満忠実性は点付き空間の写像空間を比較しない。

:::

# 5.5.3 The ∞-Category of ∞-Categories

%%%
number := false
tag := "kerodon-5-5-3"
%%%

Kerodon [Tag 0208](https://kerodon.net/tag/0208)

:::definition "kerodon_5_5_3_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.qCat_sHom_kanComplex, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.quasicategoryCore_kanComplex, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QuasicategoryObject, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.qCat_simplicialCategory, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.qCat_sHom") (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1")
Kerodon Construction 5.5.3.1（[Tag 0209](https://kerodon.net/tag/0209)）。対応表の状態：本体にある。

QuasicategoryObjectとQCatは小さい準圏を対象とし、qCat\_sHomはHomがFunctor空間のcoreに一致すると明示する。qCat\_simplicialCategoryはcore関手で合成を移送し、CatInfinityはそのcoherent nerve。原文の全構成を直接与える。

:::

:::proposition "kerodon_5_5_3_3" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catInfinity_quasicategory, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.quasicategoryCore_kanComplex, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.qCat_sHom_kanComplex")
Kerodon Proposition 5.5.3.3（[Tag 020B](https://kerodon.net/tag/020B)）。対応表の状態：本体にある。

仮定：小さい ∞ 圏の単体豊穣圏 QCat の coherent nerve（Kerodon と一致）。結論：CatInfinity が Quasicategory（一致）。

:::

:::proposition "kerodon_5_5_3_9" (uses := "kerodon_1_4_0_1, kerodon_4_4_3_1")
Kerodon Remark 5.5.3.9（[Tag 05Q1](https://kerodon.net/tag/05Q1)）。対応表の状態：一部。

quasicategoryCoreFunctorは原文のcoreの対象・通常の射への作用を直接与え、準圏上では値がKan。豊穣Hom上の作用とcoherent nerve間の射への組立ては含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.quasicategoryCore_kanComplex`

:::

:::definition "kerodon_5_5_3_11" (uses := "kerodon_1_4_0_1")
Kerodon Variant 5.5.3.11（[Tag 03UT](https://kerodon.net/tag/03UT)）。対応表の状態：なし。

CatInfinity.\{u\}は宇宙による小ささ。原文の指定κのκ-smallを満たす頂点で張るfull subcategoryとκ⁺の型への対応がない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity`

:::

:::definition "kerodon_5_5_3_13" (uses := "kerodon_1_2_5_1, kerodon_1_4_0_1")
Kerodon Variant 5.5.3.13（[Tag 03UV](https://kerodon.net/tag/03UV)）。対応表の状態：なし。

SpaceInfinity.\{u\}は宇宙版であり、原文の数値κとκ⁺で指定したKan複体のfull subcategoryへの比較がない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity`

:::

:::proposition "kerodon_5_5_3_15"
Kerodon Proposition 5.5.3.15（[Tag 06T5](https://kerodon.net/tag/06T5)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：n＝0・通常圏の nerve・QC の対角・完全忠実性・切断と小ささを照合。QC の射としての n-truncation と対象対の写像空間の条件。CatInfinity の fully faithful は写像空間の同値に関する別述語。

:::

:::corollary "kerodon_5_5_3_16"
Kerodon Corollary 5.5.3.16（[Tag 06T6](https://kerodon.net/tag/06T6)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：n＝0・通常圏の nerve・QC の対角・完全忠実性・切断と小ささを照合。QC 内の mono と、充満忠実性や像での同型の条件との同値。SSet.Mono は各次数での集合の単射。

:::

:::corollary "kerodon_5_5_3_17"
Kerodon Corollary 5.5.3.17（[Tag 04W6](https://kerodon.net/tag/04W6)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：n＝0・通常圏の nerve・QC の対角・完全忠実性・切断と小ささを照合。充満忠実な F を QC の辺として見たときの ∞ 圏の mono 性。fully faithful は F 自体の写像空間だけに関する。

:::

:::corollary "kerodon_5_5_3_19"
Kerodon Corollary 5.5.3.19（[Tag 06T7](https://kerodon.net/tag/06T7)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：n＝0・通常圏の nerve・QC の対角・完全忠実性・切断と小ささを照合。QC の対象としての C の n-truncation と局所 n-truncation を結ぶ同値条件。通常の coskeletal や π 群の型では QC の写像空間を評価しない。

:::

:::corollary "kerodon_5_5_3_21"
Kerodon Corollary 5.5.3.21（[Tag 05EW](https://kerodon.net/tag/05EW)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：n＝0・通常圏の nerve・QC の対角・完全忠実性・切断と小ささを照合。QC の対象の n-truncation から局所 n-truncation への含意と条件付きの逆。局所条件だけを述べる補題では QC の対象としての述語がない。

:::

# 5.5.4 The ∞-Bicategory of ∞-Categories

%%%
number := false
tag := "kerodon-5-5-4"
%%%

Kerodon [Tag 020J](https://kerodon.net/tag/020J)

:::definition "kerodon_5_5_4_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QuasicategoryObject, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.quasicategoryObject_enrichedCategory, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.quasicategoryObject_simplicialCategory, CategoryTheory.SimplicialNerve")
Kerodon Construction 5.5.4.1（[Tag 020K](https://kerodon.net/tag/020K)）。対応表の状態：本体にある。

仮定：小さな ∞ 圏を QuasicategoryObject として束ねる。SimplicialNerve は任意の単体豊穣圏を取れる（Kerodon と一致）。結論：quasicategoryObject\_enrichedCategory は Hom に内部 Hom Fun(C,D) を取り、SimplicialNerve をこの豊穣圏に適用すると太字 QC の単体集合を得る（一致）。

:::

:::proposition "kerodon_5_5_4_2" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_1_5_3_7, kerodon_5_4_8_1")
Kerodon Proposition 5.5.4.2（[Tag 020L](https://kerodon.net/tag/020L)）。対応表の状態：なし。

CatInfinityはHomのcoreを取った局所Kanな圏のnerve。原文の太字QCはcoreを取る前の関手準圏をHomに持つ別の対象であり、その∞-bicategory性ではない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity`

:::

:::definition "kerodon_5_5_4_9"
Kerodon Variant 5.5.4.9（[Tag 03UX](https://kerodon.net/tag/03UX)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：局所 Kan・core の場合・濃度と universe lift・通常双圏と Duskinを照合。本質的 κ-small な対象で張る太字 QC\_\{\<κ\} の ∞-bicategory。宇宙上限の lift と、任意の濃度 κ での部分圏を区別した。

:::

# 5.5.5 ∞-Categories with a Distinguished Object

%%%
number := false
tag := "kerodon-5-5-5"
%%%

Kerodon [Tag 020S](https://kerodon.net/tag/020S)

:::definition "kerodon_5_5_5_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointKanObject, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder, SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex")
Kerodon Construction 5.5.5.1（[Tag 020T](https://kerodon.net/tag/020T)）。対応表の状態：本体にある。

仮定：小さな ∞ 圏の圏 CatInfinity と、その頂点としての Δ⁰（Kerodon と一致）。結論：sliceUnder は指定した図式を固定する join の延長を束ねる。Δ⁰ を表す pointKanObject の基礎単体集合を CatInfinity の頂点に取り、原文の QC の coslice を得る（一致）。

:::

:::proposition "kerodon_5_5_5_2" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catInfinity_quasicategory, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceUnderProjection_leftFibration, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceUnder_quasicategory")
Kerodon Proposition 5.5.5.2（[Tag 020U](https://kerodon.net/tag/020U)）。対応表の状態：本体にある。

仮定：Quasicategory X と図式 p:K→X（Lean が弱い：CatInfinity の一点に限らず任意の図式）。結論：sliceUnder\_quasicategory は coslice の ∞ 圏性、sliceUnderProjection\_leftFibration は X への射影の左ファイブレーション性（一致）。

:::

:::proposition "kerodon_5_5_5_6"
Kerodon Proposition 5.5.5.6（[Tag 020Y](https://kerodon.net/tag/020Y)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：空間値に制限・一点の QC coslice と輸送・普通の双圏の Pithを照合。点付き QCat の hc nerve と QC\_\* の全空間を結ぶ比較の ∞ 圏同値。relativeHomCosliceComparison は left fibration 分類圏の固定対象上の比較。

:::

:::definition "kerodon_5_5_5_8"
Kerodon Construction 5.5.5.8（[Tag 0210](https://kerodon.net/tag/0210)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：空間値に制限・一点の QC coslice と輸送・普通の双圏の Pithを照合。太字 QC の Δ⁰ 上の coslice としての太字 QC\_Obj。通常の QC の coslice では 2-射の情報を落とす。

:::

:::proposition "kerodon_5_5_5_9" (uses := "kerodon_1_1_0_6, kerodon_5_4_3_1, kerodon_5_4_3_4, kerodon_5_5_4_2")
Kerodon Proposition 5.5.5.9（[Tag 0211](https://kerodon.net/tag/0211)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：空間値に制限・一点の QC coslice と輸送・普通の双圏の Pithを照合。太字 QC\_Obj が ∞-bicategory で太字 QC への射が interior fibration。普通の coslice 射影は interior を述べない。

:::

:::definition "kerodon_5_5_5_10" (uses := "kerodon_5_4_5_1")
Kerodon Definition 5.5.5.10（[Tag 0212](https://kerodon.net/tag/0212)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：空間値に制限・一点の QC coslice と輸送・普通の双圏の Pithを照合。太字 QC\_Obj の Pith としての QC\_Obj。quasicategory core は Pith と違い可逆辺で切る。

:::

:::proposition "kerodon_5_5_5_11" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_5_1_4_1, kerodon_5_4_5_6, kerodon_5_4_7_10, kerodon_5_4_7_11, kerodon_5_5_5_9")
Kerodon Proposition 5.5.5.11（[Tag 0213](https://kerodon.net/tag/0213)）。対応表の状態：なし。

pointedSpaceProjectionの全空間は空間のcoslice。原文はQCの対象を分類する全空間であり、空間側が指定四角のpullbackである比較なしには同じ射の特殊化ではない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection_leftFibration`

:::

:::proposition "kerodon_5_5_5_14" (uses := "kerodon_5_1_4_1, kerodon_5_2_8_9, kerodon_5_4_9_2, kerodon_5_5_5_11")
Kerodon Proposition 5.5.5.14（[Tag 02S5](https://kerodon.net/tag/02S5)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：空間値に制限・一点の QC coslice と輸送・普通の双圏の Pithを照合。QC\_Obj→QC の homotopy transport と hQC→hQCat の指定した同値。一般の homotopyTransport はこの普遍 fibration を指定しない。

:::

