import Verso
import VersoManual
import VersoBlueprint
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.CocartesianStrictTransport
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.CocartesianStrictTransportEquivalence
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.Comparison
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.Definition
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.F1BCocartesianScaffoldUniversalScaffold
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.InitialSectionLifting
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.LeftFibrationInitialEvaluation
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.LeftScaffold
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.LeftStrictTransportReconstruction
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.LeftStrictTransportWeightedNerve
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.Nerve
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.NerveCocartesianScaffold
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.NerveCocartesianUnit
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.NerveLeftFibration
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.NerveUnderMap
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.ScaffoldIntervalPushout
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialReplacement
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialReplacementBaseChange
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialReplacementFiber
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialReplacementFunctor
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.StrictDiagramScaffoldAdjunction
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.StrictDiagramScaffoldIdentities
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.StrictTransportEnriched
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.StrictTransportMappingEquivalence
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.TautScaffold
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.RelativeFunctor

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "5.3 Fibrations over Ordinary Categories" =>
%%%
number := false
tag := "kerodon-5-3"
%%%

Kerodon の 5.3 節（[Tag 035A](https://kerodon.net/tag/035A)）の項目と、SerrePositivity・Mathlib の宣言との対応。本文は対応表（research/kerodon-coverage）の判定の理由の要約で、Kerodon の本文の写しではない。

# 5.3.1 The Strict Transport Representation

%%%
number := false
tag := "kerodon-5-3-1"
%%%

Kerodon [Tag 035D](https://kerodon.net/tag/035D)

:::definition "kerodon_5_3_1_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram")
Kerodon Construction 5.3.1.1（[Tag 035E](https://kerodon.net/tag/035E)）。対応表の状態：本体にある。

仮定：通常の圏 C と任意の p:E→N(C)（Kerodon と一致）。結論：値が Fun\_\{/N(C)\}(N(Under c),E) で、底の射に Under の前合成を用いる単体集合値関手（一致）。

:::

:::definition "kerodon_5_3_1_5" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransport, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransportDiagram, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.nerveUnderMap")
Kerodon Construction 5.3.1.5（[Tag 035J](https://kerodon.net/tag/035J)）。対応表の状態：本体にある。

仮定：通常の圏 C、cocartesian fibration p:E→N(C)（Lean が弱い：単体集合値の図式の構成には p の性質を仮定しない）。結論：弱輸送の値を全辺を cocartesian へ送る相対関手が張る全部分複体に制限し、c の関手を作る（一致）。

:::

:::proposition "kerodon_5_3_1_7" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransportEvaluate_isQCatEquivalence, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransportEvaluate_trivialKanFibration") (uses := "kerodon_1_4_0_1, kerodon_5_1_4_1, kerodon_5_3_1_22")
Kerodon Proposition 5.3.1.7（[Tag 035L](https://kerodon.net/tag/035L)）。対応表の状態：本体にある。

cocartesianStrictTransportEvaluate\_trivialKanFibrationは原文の同じstrict transportの各恒等射評価がtrivial Kan fibrationという結論全体。原文には輸送の自然性を要求する追加結論はなく、従来のpartialの理由を訂正する。

:::

:::corollary "kerodon_5_3_1_8"
Kerodon Corollary 5.3.1.8（[Tag 035M](https://kerodon.net/tag/035M)）。対応表の状態：一部。

cocartesianStrictTransportEvaluate\_isQCatEquivalenceは原文の指定された自然同型の各対象の成分が同値であることを直接与える。辺との自然性と成分の組立ては含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransportEvaluate_isQCatEquivalence`

:::

:::corollary "kerodon_5_3_1_9"
Kerodon Corollary 5.3.1.9（[Tag 035N](https://kerodon.net/tag/035N)）。対応表の状態：一部。

標的U′をleft fibrationに制限するとstrictTransportPostToLeftFibrationが同じcocartesian strict transport間の後合成を直接構成し、原文(2)の制限を与える。一般の標的とiff全体は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictTransportPost`、`SerrePositivity.KST.Fibration.strictTransportPostToLeftFibration`

:::

:::definition "kerodon_5_3_1_10" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.cocartesianRelativeFunctorSpace, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.cocartesianRelativeFunctorPredicate")
Kerodon Notation 5.3.1.10（[Tag 02T1](https://kerodon.net/tag/02T1)）。対応表の状態：本体にある。

仮定：共通の底上の二つの cocartesian fibration（Lean が弱い：構成は任意の p,q）。結論：相対関手空間のうち始域の cocartesian 辺を標的の cocartesian 辺へ送る頂点が張る全部分複体（一致）。

:::

:::definition "kerodon_5_3_1_11"
Kerodon Variant 5.3.1.11（[Tag 02T2](https://kerodon.net/tag/02T2)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：恒等射での評価・辺ごとの輸送と hQCat・通常圏の輸送を照合。相対関手圏で cartesian 辺を保つ頂点で張る充満部分圏と cartesian section の記法。coCartesian 用の section だけでは反対側の定義がそろわない。

:::

:::proposition "kerodon_5_3_1_21" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_4_2_5_4, kerodon_4_5_1_22, kerodon_4_5_6_20, kerodon_4_8_4_6, kerodon_5_1_4_1")
Kerodon Proposition 5.3.1.21（[Tag 035S](https://kerodon.net/tag/035S)）。対応表の状態：一部。

Uをleft fibrationに制限すると全辺はcocartesianで、相対Functor空間とcocartesian section空間は同じ条件になる。trivialKanFibration\_relativeHom\_of\_leftAnodyneは同じ制限射のtrivial Kan性を直接返す。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.trivialKanFibration_relativeHom_of_leftAnodyne`

:::

:::corollary "kerodon_5_3_1_22" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.InitialSectionLifting.cocartesianSectionsEvaluate_trivialKanFibration, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorEvaluate_initial_trivialKanFibration")
Kerodon Corollary 5.3.1.22（[Tag 035T](https://kerodon.net/tag/035T)）。対応表の状態：本体にある。

仮定：底が ∞ 圏、p は cocartesian fibration、a:A→B は左ファイブレーションで A に始頂点 v（Lean が弱い：全辺を保つ sections の補題自体は a に左ファイブレーション性を要求しない）。結論：v での評価が自明 Kan ファイブレーション。a が左ファイブレーションなら a の全辺が cocartesian なので相対関手条件が一致（一致）。

:::

:::corollary "kerodon_5_3_1_23" (uses := "kerodon_1_1_0_6, kerodon_5_1_4_1, kerodon_5_3_1_22")
Kerodon Corollary 5.3.1.23（[Tag 02TC](https://kerodon.net/tag/02TC)）。対応表の状態：一部。

C\^◁を準圏と仮定すれば、そのcone pointをIsInitialVertexとしてcocartesianSectionsEvaluate\_trivialKanFibrationに代入し、同じ評価射のtrivial Kan性を直接得る。一般の単体集合Cの錐は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.InitialSectionLifting.cocartesianSectionsEvaluate_trivialKanFibration`

:::

# 5.3.2 Homotopy Colimits of Simplicial Sets

%%%
number := false
tag := "kerodon-5-3-2"
%%%

Kerodon [Tag 035U](https://kerodon.net/tag/035U)

:::definition "kerodon_5_3_2_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacement, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementFunctor")
Kerodon Construction 5.3.2.1（[Tag 035V](https://kerodon.net/tag/035V)）。対応表の状態：本体にある。

仮定：通常の圏 C と単体集合値図式 F（Kerodon と一致）。結論：単体が (σ:\[n\]→C, τ∈F(σ0)\_n) の simplicialReplacement と nerve への射影を作る。Over(N(C)) 値の関手性もある（一致）。

:::

:::proposition "kerodon_5_3_2_2" (uses := "kerodon_1_1_0_6")
Kerodon Example 5.3.2.2（[Tag 035W](https://kerodon.net/tag/035W)）。対応表の状態：一部。

添字圏が一点である場合、simplicialReplacementConstantLift\_isIsoはその唯一のF(c)から同じhomotopy colimitへの射が同型と直接返す。任意の離散圏の直和は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementConstantLift_isIso`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementConstantIso`

:::

:::proposition "kerodon_5_3_2_3" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementBaseMap, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementBaseMap_isPullback")
Kerodon Remark 5.3.2.3（[Tag 035X](https://kerodon.net/tag/035X)）。対応表の状態：本体にある。

仮定：通常の圏の関手 H:D→C と単体集合値図式 F（Kerodon と一致）。結論：置換の射影と nerveMap H の比較正方形が引き戻し。D が一点なら F(c) のファイバー比較（一致）。

:::

:::definition "kerodon_5_3_2_11" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacement")
Kerodon Notation 5.3.2.11（[Tag 0365](https://kerodon.net/tag/0365)）。対応表の状態：本体にある。

仮定：\[n\] 上の単体集合値図式（Lean が弱い：添字圏は任意）。結論：simplicialReplacement を \[n\] に適用した単体集合が mapping simplex（一致）。

:::

:::proposition "kerodon_5_3_2_12" (uses := "kerodon_1_1_0_6")
Kerodon Remark 5.3.2.12（[Tag 0252](https://kerodon.net/tag/0252)）。対応表の状態：なし。

assemblyの構成と添字変更のpullbackは、原文の始点を除いた鎖と貼り合わせる指定四角のpushout性とは別の主張。射があるだけをそのcomponentとしない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementAssembly`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementAssembly_baseMap_isPullback`

:::

:::proposition "kerodon_5_3_2_13" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementIntervalIso, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldInterval_isPushout")
Kerodon Example 5.3.2.13（[Tag 0366](https://kerodon.net/tag/0366)）。対応表の状態：本体にある。

仮定：\[1\] に当たる ULift(Fin 2) 上の単体集合値図式 F（Kerodon と一致）。結論：simplicialReplacement F は Δ¹×F(0) を終端で F(1) に貼る押し出しと同型（一致）。

:::

:::proposition "kerodon_5_3_2_17"
Kerodon Proposition 5.3.2.17（[Tag 036B](https://kerodon.net/tag/036B)）。対応表の状態：一部。

図式をKan値、各成分をIsQCatEquivalenceに強めれば、simplicialReplacementMap\_isPrecompositionEquivalenceとIsPrecompositionEquivalence.isWeakHomotopyEquivalenceから同じ全空間射の弱ホモトピー同値が直接得られる。一般の単体集合値ではない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementMap_isPrecompositionEquivalence`、`SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsPrecompositionEquivalence.isWeakHomotopyEquivalence`、`SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.isWeakHomotopyEquivalence_iff_isQCatEquivalence`

:::

:::definition "kerodon_5_3_2_18" (uses := "kerodon_1_1_0_6, kerodon_4_5_5_14, kerodon_4_8_8_14, kerodon_5_3_2_2, kerodon_5_3_2_3, kerodon_5_3_2_12")
Kerodon Variant 5.3.2.18（[Tag 036C](https://kerodon.net/tag/036C)）。対応表の状態：一部。

図式をKan値に強めるとsimplicialReplacementMap\_isPrecompositionEquivalenceは原文の同じ自然変換のhomotopy colimitへの誘導射を圏同値と直接返す。一般の単体集合値図式には及ばない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementMap_isPrecompositionEquivalence`

:::

:::definition "kerodon_5_3_2_19" (uses := "kerodon_1_1_0_6")
Kerodon Construction 5.3.2.19（[Tag 036D](https://kerodon.net/tag/036D)）。対応表の状態：一部。

simplicialReplacementUnderEvaluationは原文の各cについての同じN(Under c)×F(c)からhomotopy colimitへの射f\_cを直接構成する。currying後の自然変換全体は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementUnderEvaluation`

:::

:::proposition "kerodon_5_3_2_20" (uses := "kerodon_1_1_0_6, kerodon_5_3_2_19")
Kerodon Proposition 5.3.2.20（[Tag 036E](https://kerodon.net/tag/036E)）。対応表の状態：なし。

strictDiagramMappingScaffoldIsoは相対Functor空間との同型。原文は絶対Functor空間と指定Gの豊穣Homの同型であり、同じ対象へ比較する型がない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingScaffoldIso`

:::

:::corollary "kerodon_5_3_2_21"
Kerodon Corollary 5.3.2.21（[Tag 036F](https://kerodon.net/tag/036F)）。対応表の状態：なし。

引用はE→N(C)を指定した相対Homの全単射。原文の絶対的な右随伴の指定Gとは異なり、自然性もこの型にはない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramScaffoldHomEquiv`

:::

:::corollary "kerodon_5_3_2_22" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramScaffoldHomEquiv, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingScaffoldIso")
Kerodon Corollary 5.3.2.22（[Tag 036G](https://kerodon.net/tag/036G)）。対応表の状態：本体にある。

仮定：通常の圏 C、単体集合値図式 F、任意の q:E→N(C)（Kerodon と一致）。結論：置換から E への相対関手空間と、F から弱輸送図式への豊穣 Hom の同型。Lean の同型は逆向きに表示（一致）。

:::

:::corollary "kerodon_5_3_2_23"
Kerodon Corollary 5.3.2.23（[Tag 036H](https://kerodon.net/tag/036H)）。対応表の状態：一部。

strictDiagramScaffoldHomEquivは原文と同じhomotopy colimitを始域とする底上の射と、weak transportへの自然変換のHom全単射を直接与える。両変数の自然性・随伴としての構造全体は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramScaffoldHomEquiv`

:::

# 5.3.3 The Weighted Nerve

%%%
number := false
tag := "kerodon-5-3-3"
%%%

Kerodon [Tag 025W](https://kerodon.net/tag/025W)

:::definition "kerodon_5_3_3_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection")
Kerodon Definition 5.3.3.1（[Tag 025X](https://kerodon.net/tag/025X)）。対応表の状態：本体にある。

仮定：通常の圏 C と単体集合値図式 F（Kerodon と一致）。結論：weightedNerve の単体は鎖 σ と整合する初期区間ごとの F の単体。射影は σ を取る（一致）。

:::

:::proposition "kerodon_5_3_3_15" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_5_1_1_1, kerodon_5_1_4_1, kerodon_5_1_4_8, kerodon_5_2_3_17")
Kerodon Proposition 5.3.3.15（[Tag 046X](https://kerodon.net/tag/046X)）。対応表の状態：一部。

Gを定値Δ⁰、Fを準圏値に制限するとweightedNerveProjection\_cocartesianFibrationは原文(1)の同じ射を直接扱う。一般の相対weighted nerveと辺の判定は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection_cocartesianFibration`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveMap_preservesCocartesianEdges`

:::

:::corollary "kerodon_5_3_3_16" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_5_1_4_1, kerodon_5_3_3_15")
Kerodon Corollary 5.3.3.16（[Tag 046Y](https://kerodon.net/tag/046Y)）。対応表の状態：一部。

weightedNerveProjection\_cocartesianFibrationは原文(1)そのもの。底N(C)が準圏なので全空間の準圏性も従う。(2)の任意(f,e)のiffは含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection_cocartesianFibration`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveFiberMap_isIso`

:::

:::corollary "kerodon_5_3_3_18" (uses := "kerodon_1_1_0_6, kerodon_5_1_4_15, kerodon_5_3_3_15")
Kerodon Corollary 5.3.3.18（[Tag 046Z](https://kerodon.net/tag/046Z)）。対応表の状態：一部。

Gを定値Δ⁰、FをKan値に制限すればweightedNerveProjection\_leftFibrationは原文の同じ誘導射のleft fibration性を直接返す。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection_leftFibration`

:::

:::corollary "kerodon_5_3_3_19" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection_leftFibration")
Kerodon Corollary 5.3.3.19（[Tag 036N](https://kerodon.net/tag/036N)）。対応表の状態：本体にある。

仮定：通常の圏 C と各 F(c) が KanComplex の図式（Kerodon と一致）。結論：weightedNerve F→N(C) が LeftFibration（一致）。

:::

:::corollary "kerodon_5_3_3_20" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_1_3_2, kerodon_4_8_8_14, kerodon_5_1_4_1, kerodon_5_1_6_1, kerodon_5_2_4_7, kerodon_5_3_3_16")
Kerodon Corollary 5.3.3.20（[Tag 036P](https://kerodon.net/tag/036P)）。対応表の状態：一部。

両図式がKan値ならweightedNerveMap\_isPrecompositionEquivalenceは原文のlevelwise圏同値⇒同じweightedNerveMapが圏同値という方向を直接返す。任意図式と逆は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveMap_isPrecompositionEquivalence`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveMap`

:::

:::definition "kerodon_5_3_3_23" (uses := "kerodon_1_1_0_6")
Kerodon Notation 5.3.3.23（[Tag 036R](https://kerodon.net/tag/036R)）。対応表の状態：なし。

leftStrictTransportDiagramはUnderからの相対Functor空間。原文はOverのnerveのpullbackであり、さらにEからweighted nerveへの指定単位を構成する。引用は別の図式と逆向きのHom対応。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramScaffoldHomEquiv`

:::

:::proposition "kerodon_5_3_3_24" (uses := "kerodon_1_1_0_6, kerodon_5_3_3_23")
Kerodon Proposition 5.3.3.24（[Tag 036S](https://kerodon.net/tag/036S)）。対応表の状態：なし。

引用の全単射はF→strict transportとreplacement→Eの間。原文のG\_E→FとE→weighted nerveの間とは左右の対象と向きが異なる。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramScaffoldHomEquiv`

:::

:::corollary "kerodon_5_3_3_25"
Kerodon Corollary 5.3.3.25（[Tag 036T](https://kerodon.net/tag/036T)）。対応表の状態：なし。

replacementとstrict transportのHom対応は、原文のweighted nerveを右随伴とする随伴ではない。別の関手の随伴候補だけをpartialとしない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramScaffoldHomEquiv`

:::

:::definition "kerodon_5_3_3_26" (uses := "kerodon_1_1_0_6, kerodon_5_3_3_23, kerodon_5_3_3_24")
Kerodon Variant 5.3.3.26（[Tag 036U](https://kerodon.net/tag/036U)）。対応表の状態：なし。

引用はKan値weighted nerveと相対Functor空間の比較射の圏同値。原文の任意EについてのG\_Eの豊穣Homとの厳密同型は別の射であり、同値でもその成分ではない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.strictTransportWeightedNerveMappingSpaceMap_isQCatEquivalence`

:::

# 5.3.4 Scaffolds of Cocartesian Fibrations

%%%
number := false
tag := "kerodon-5-3-4"
%%%

Kerodon [Tag 036V](https://kerodon.net/tag/036V)

:::definition "kerodon_5_3_4_1" (uses := "kerodon_1_1_0_6")
Kerodon Definition 5.3.4.1（[Tag 036W](https://kerodon.net/tag/036W)）。対応表の状態：一部。

cocartesianScaffoldHorizontalEdgeは任意のF・底射f・頂点xから、係数が退化辺const xである原文の水平辺を直接構成する。全ての辺が水平であるための判定は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianScaffoldHorizontalEdge`

:::

:::definition "kerodon_5_3_4_2" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_5_1_1_1, kerodon_5_1_4_1, kerodon_5_3_2_1")
Kerodon Definition 5.3.4.2（[Tag 0255](https://kerodon.net/tag/0255)）。対応表の状態：一部。

各F(c)を準圏に強めたCocartesianScaffoldは底上の等式・水平辺のcocartesian性・全fiberの同値という原文三条件を同じλに課す。一般の単体集合値は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.CocartesianScaffold`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.IsLeftScaffold`

:::

:::definition "kerodon_5_3_4_7" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianUniversalScaffold")
Kerodon Construction 5.3.4.7（[Tag 026D](https://kerodon.net/tag/026D)）。対応表の状態：本体にある。

仮定：通常の圏 C と cocartesian fibration p:E→N(C)（Lean が弱い：写像の構成は任意の p に定義）。結論：strict transport 図式の simplicialReplacement を鎖上で評価して E に送る universal scaffold（一致）。

:::

:::proposition "kerodon_5_3_4_8" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianUniversalScaffold_isCocartesianScaffold, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.universalScaffold_isLeftScaffold")
Kerodon Proposition 5.3.4.8（[Tag 0370](https://kerodon.net/tag/0370)）。対応表の状態：本体にある。

仮定：通常の圏 C と cocartesian fibration p:E→N(C)（Kerodon と一致）。結論：その strict transport の universal scaffold が CocartesianScaffold（一致）。

:::

:::corollary "kerodon_5_3_4_9" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianUniversalScaffold_isCocartesianScaffold")
Kerodon Corollary 5.3.4.9（[Tag 0371](https://kerodon.net/tag/0371)）。対応表の状態：本体にある。

仮定：通常の圏 C と cocartesian fibration p:E→N(C)（Kerodon と一致）。結論：各値が ∞ 圏の strict transport 図式と、その置換からの CocartesianScaffold を具体的に与える（一致）。

:::

:::definition "kerodon_5_3_4_11" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.tautScaffold, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.tautScaffoldDiagram")
Kerodon Construction 5.3.4.11（[Tag 0373](https://kerodon.net/tag/0373)）。対応表の状態：本体にある。

仮定：通常の圏 C と任意の単体集合値図式 F（Kerodon と一致）。結論：置換の単体 (σ,τ) を τ の各初期区間を F の射で輸送した weightedNerve の単体へ送る tautScaffold（一致）。

:::

:::proposition "kerodon_5_3_4_12" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.tautScaffold_projection")
Kerodon Remark 5.3.4.12（[Tag 0374](https://kerodon.net/tag/0374)）。対応表の状態：本体にある。

仮定：通常の圏 C と任意の単体集合値図式 F（Kerodon と一致）。結論：tautScaffold F と weightedNerveProjection F の合成が simplicialReplacementProjection F（一致）。

:::

:::proposition "kerodon_5_3_4_14" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.tautScaffold_map, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.tautScaffold_baseMap_isPullback")
Kerodon Remark 5.3.4.14（[Tag 0376](https://kerodon.net/tag/0376)）。対応表の状態：本体にある。

仮定：通常の圏の関手 H:D→C と図式 F（Kerodon と一致）。結論：tautScaffold (H⋙F) が tautScaffold F の底変換となる引き戻し正方形（一致）。

:::

:::proposition "kerodon_5_3_4_15" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.tautScaffoldFiberMap_isIso")
Kerodon Example 5.3.4.15（[Tag 026E](https://kerodon.net/tag/026E)）。対応表の状態：本体にある。

仮定：通常の圏 C、図式 F、底の対象 c（Kerodon と一致）。結論：tautScaffold が誘導する c 上のファイバーの射が同型（一致）。

:::

:::proposition "kerodon_5_3_4_17" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.tautScaffold_isCocartesianScaffold, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.tautScaffold_isLeftScaffold")
Kerodon Proposition 5.3.4.17（[Tag 0379](https://kerodon.net/tag/0379)）。対応表の状態：本体にある。

仮定：通常の圏 C と各値が Quasicategory の図式 F（Kerodon と一致）。結論：tautScaffold F が weightedNerveProjection F に対する CocartesianScaffold（一致）。

:::

:::corollary "kerodon_5_3_4_18" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_1_3_2, kerodon_5_1_4_1, kerodon_5_3_4_17")
Kerodon Corollary 5.3.4.18（[Tag 037A](https://kerodon.net/tag/037A)）。対応表の状態：一部。

図式を準圏値に強めればtautScaffold\_isCocartesianScaffoldは同じFのweighted nerve射影とtaut scaffoldを直接与える。一般図式は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.tautScaffold_isCocartesianScaffold`

:::

:::corollary "kerodon_5_3_4_19" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveCocartesianTransportUnit, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveCocartesianTransportUnit_isQCatEquivalence")
Kerodon Corollary 5.3.4.19（[Tag 037B](https://kerodon.net/tag/037B)）。対応表の状態：本体にある。

仮定：通常圏 C と、各値が Quasicategory の単体集合値図式 F（QCat 値）（Kerodon と一致）。結論：weighted nerve 射影に対する cocartesian strict transport への自然変換 F→sTr を与え、全ての成分が IsQCatEquivalence（一致）。

:::

:::proposition "kerodon_5_3_4_20"
Kerodon Proposition 5.3.4.20（[Tag 037C](https://kerodon.net/tag/037C)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：定値・同型の図式・成分別の同値・ホモトピー余極限からの比較を照合。各 F(u) が left covering のとき hocolim から weighted nerve への λ\_t が同型。tautScaffold の一般の前合成同値や左ファイブレーション性はこの厳密同型ではない。

:::

:::corollary "kerodon_5_3_4_22"
Kerodon Corollary 5.3.4.22（[Tag 037E](https://kerodon.net/tag/037E)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：定値・同型の図式・成分別の同値・ホモトピー余極限からの比較を照合。全ての作用が単体集合の同型の図式で λ\_t の厳密な性質を主張。定値図式での weighted nerve の同型は非定値な同型図式を含まない。

:::

:::corollary "kerodon_5_3_4_23"
Kerodon Corollary 5.3.4.23（[Tag 037F](https://kerodon.net/tag/037F)）。対応表の状態：一部。

添字groupoidを一点に限るとsimplicialReplacementPoint\_kanComplexは同じhomotopy colimitのKan性を直接返す。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementPoint_kanComplex`

:::

# 5.3.5 Application: Classification of Cocartesian Fibrations

%%%
number := false
tag := "kerodon-5-3-5"
%%%

Kerodon [Tag 037H](https://kerodon.net/tag/037H)

:::definition "kerodon_5_3_5_1" (uses := "kerodon_1_4_0_1, kerodon_4_5_7_1")
Kerodon Definition 5.3.5.1（[Tag 037J](https://kerodon.net/tag/037J)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Kan 値・左ファイブレーション・成分ごとの同値と合成・1圏の Grothendieckを照合。QCat 値の図式間の levelwise equivalence のジグザグによる述語。単一の componentwise 比較とは同値関係の定義が異なる。

:::

:::proposition "kerodon_5_3_5_2" (uses := "kerodon_5_1_4_1, kerodon_5_1_7_1, kerodon_5_3_3_20, kerodon_5_3_4_11, kerodon_5_3_5_1")
Kerodon Proposition 5.3.5.2（[Tag 037K](https://kerodon.net/tag/037K)）。対応表の状態：なし。

引用は一つのKan値図式のweighted nerveとstrict transportの合成のunit同型。原文の任意の二図式のlevelwiseジグザグ同値と相対fibration同値のiffは直接述べない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.strictTransportWeightedNerveTransportIso`

:::

:::corollary "kerodon_5_3_5_3"
Kerodon Corollary 5.3.5.3（[Tag 037L](https://kerodon.net/tag/037L)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Kan 値・左ファイブレーション・成分ごとの同値と合成・1圏の Grothendieckを照合。QCat 値の図式の levelwise equivalence の反射・対称・推移。単一の自然変換の成分ごとの QCat 同値の合成則ではジグザグの述語を定めない。

:::

:::theorem "kerodon_5_3_5_6" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_5_3_35, kerodon_4_5_4_9, kerodon_5_1_4_1, kerodon_5_1_7_5, kerodon_5_3_4_7, kerodon_5_3_4_11, kerodon_5_3_5_2, kerodon_5_3_5_8, kerodon_5_3_5_9")
Kerodon Theorem 5.3.5.6（[Tag 037P](https://kerodon.net/tag/037P)）。対応表の状態：なし。

引用はstrict transportの∞圏での同値やscaffoldの比較。原文のlevelwise equivalenceのジグザグ商とfibrationの相対逆による商の全単射へ移す比較は引用型にない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransportInfinityMap_isQCatEquivalence`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianUniversalScaffold_isPrecompositionEquivalence`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportTotalEquivalence`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveCocartesianTransportUnit_isQCatEquivalence`

:::

:::theorem "kerodon_5_3_5_7" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_1_5_7_5, kerodon_4_1_1_10, kerodon_4_3_6_5, kerodon_4_3_7_8, kerodon_4_5_3_35, kerodon_4_5_4_9, kerodon_4_8_8_14, kerodon_5_1_1_1, kerodon_5_1_4_1, kerodon_5_1_6_2, kerodon_5_2_4_1, kerodon_5_3_2_12, kerodon_5_3_4_18")
Kerodon Theorem 5.3.5.7（[Tag 037Q](https://kerodon.net/tag/037Q)）。対応表の状態：一部。

Fを準圏値に強めるとCocartesianScaffold.isPrecompositionEquivalenceは同じλに対する原文(1)⇒(2)を直接返す。任意の図式と逆方向は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.CocartesianScaffold.isPrecompositionEquivalence`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianUniversalScaffold_isPrecompositionEquivalence`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.tautScaffold_isPrecompositionEquivalence_of_quasicategory`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.CocartesianScaffold`

:::

:::corollary "kerodon_5_3_5_8" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianUniversalScaffold_isPrecompositionEquivalence, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.tautScaffold_isPrecompositionEquivalence_of_quasicategory, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveCocartesianTransportUnit_isQCatEquivalence, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportTotalEquivalence") (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_5_1_4_1, kerodon_5_3_1_5, kerodon_5_3_4_7, kerodon_5_3_4_8, kerodon_5_3_5_7")
Kerodon Corollary 5.3.5.8（[Tag 037R](https://kerodon.net/tag/037R)）。対応表の状態：本体にある。

cocartesianUniversalScaffold\_isPrecompositionEquivalenceは原文の同じuniversal scaffold λ\_uそのものの圏同値性を全てのcocartesian fibrationについて直接返す。原文はweighted nerveへの復元を結論していないので従来のpartial理由を訂正する。

:::

:::corollary "kerodon_5_3_5_9" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_1_3_2, kerodon_5_1_4_1, kerodon_5_3_2_18, kerodon_5_3_3_20, kerodon_5_3_4_11, kerodon_5_3_4_17, kerodon_5_3_5_7")
Kerodon Corollary 5.3.5.9（[Tag 037S](https://kerodon.net/tag/037S)）。対応表の状態：一部。

Fを準圏値に強めればtautScaffold\_isPrecompositionEquivalence\_of\_quasicategoryは原文の同じλ\_tの圏同値性を直接返す。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.tautScaffold_isPrecompositionEquivalence_of_quasicategory`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.tautScaffold_isPrecompositionEquivalence`

:::

:::corollary "kerodon_5_3_5_11"
Kerodon Corollary 5.3.5.11（[Tag 037U](https://kerodon.net/tag/037U)）。対応表の状態：なし。

引用のcocartesianStrictTransportMappingSpaceMapはcocartesian辺を保つ射の空間と両方strict transportの豊穣Homの比較。原文は全相対Functor空間と標的weak transportへのHomで、同じθである比較がない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransportMappingSpaceMap_isQCatEquivalence`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransportInfinityMap_isFullyFaithful`

:::

:::corollary "kerodon_5_3_5_12" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransportMappingSpaceMap_isQCatEquivalence, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransportInfinityMap_isFullyFaithful")
Kerodon Corollary 5.3.5.12（[Tag 037V](https://kerodon.net/tag/037V)）。対応表の状態：本体にある。

仮定：同じ通常の圏の nerve 上の二つの cocartesian fibration p,q（Kerodon と一致）。結論：cocartesian 相対関手空間から strict transport 図式間の豊穣 Hom への比較が IsQCatEquivalence（一致）。

:::

# 5.3.6 Application: Relative Exponentials

%%%
number := false
tag := "kerodon-5-3-6"
%%%

Kerodon [Tag 037W](https://kerodon.net/tag/037W)

:::proposition "kerodon_5_3_6_1" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_1_3_2, kerodon_4_5_3_33, kerodon_4_5_8_10, kerodon_5_1_4_1, kerodon_5_1_4_9, kerodon_5_3_6_6")
Kerodon Proposition 5.3.6.1（[Tag 025H](https://kerodon.net/tag/025H)）。対応表の状態：一部。

cocartesian側、C′=C、底の圏同値をinner anodyneに制限すると、引用は同じpullback projectionの圏同値性を直接返す。一般のcategorical equivalence全体は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianFibration_pullback_innerAnodyne_isPrecompositionEquivalence`

:::

:::lemma_ "kerodon_5_3_6_3" (uses := "kerodon_1_1_0_6, kerodon_1_5_4_13, kerodon_4_2_5_3, kerodon_5_3_2_3, kerodon_5_3_2_12")
Kerodon Lemma 5.3.6.3（[Tag 025A](https://kerodon.net/tag/025A)）。対応表の状態：一部。

添字を有限鎖、Bをそのnerve、fを指定inner horn包含に限ればreplacementNerveHorn\_preimage\_innerAnodyneは同じ逆像包含のinner anodyne性(2)を直接返す。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.replacementNerveHorn_preimage_innerAnodyne`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.replacementInitialSubcomplex_isPushout`

:::

:::lemma_ "kerodon_5_3_6_5" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_8_8_14, kerodon_5_1_4_1, kerodon_5_3_5_7")
Kerodon Lemma 5.3.6.5（[Tag 037X](https://kerodon.net/tag/037X)）。対応表の状態：一部。

Fを準圏値に強めればCocartesianScaffold.overPullback\_isPrecompositionEquivalenceは任意Sへの同じscaffoldの底変換射の圏同値性を直接返す。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.CocartesianScaffold.overPullback_isPrecompositionEquivalence`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianUniversalScaffold_overPullback_isPrecompositionEquivalence`

:::

:::lemma_ "kerodon_5_3_6_6" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_1_5_4_13, kerodon_4_8_8_11, kerodon_5_1_4_1, kerodon_5_3_4_9, kerodon_5_3_6_3, kerodon_5_3_6_5")
Kerodon Lemma 5.3.6.6（[Tag 02RK](https://kerodon.net/tag/02RK)）。対応表の状態：一部。

cocartesianFibration\_pullback\_innerAnodyne\_isPrecompositionEquivalenceは原文のcocartesian fibrationの場合そのもの。cartesian側は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianFibration_pullback_innerAnodyne_isPrecompositionEquivalence`

:::

:::proposition "kerodon_5_3_6_7" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_5_8_18, kerodon_5_1_1_1, kerodon_5_1_2_5, kerodon_5_1_4_1, kerodon_5_3_6_1, kerodon_5_3_6_12, kerodon_5_3_6_13")
Kerodon Proposition 5.3.6.7（[Tag 0470](https://kerodon.net/tag/0470)）。対応表の状態：一部。

Vに全単射な前合成同値に対する持ち上げを追加するとfiberwiseHomPostcomp\_innerFibrationは原文の同じV′のinner性を直接返す。cartesian fibration性の一条件のみで、cartesian辺の判定は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.fiberwiseHomPostcomp_innerFibration`

:::

:::corollary "kerodon_5_3_6_9" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_5_1_1_1, kerodon_5_1_1_4, kerodon_5_1_4_1, kerodon_5_3_6_7")
Kerodon Corollary 5.3.6.9（[Tag 0472](https://kerodon.net/tag/0472)）。対応表の状態：一部。

fiberwiseHomProjection\_cartesianFibrationは原文(1)、fiberwiseHom\_isCartesianEdge\_of\_invertingは原文(2)の十分条件を同じ射・辺について直接返す。必要条件は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.fiberwiseHomProjection_cartesianFibration`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.fiberwiseHom_isCartesianEdge_of_inverting`

:::

:::proposition "kerodon_5_3_6_10" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_5_1_1_1, kerodon_5_1_4_1, kerodon_5_2_2_4, kerodon_5_2_4_4, kerodon_5_3_6_9")
Kerodon Proposition 5.3.6.10（[Tag 0473](https://kerodon.net/tag/0473)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：片側が Kan・左ファイブレーション・反対と cartesian 判定・一点・写像の移送を照合。前項の fiberwise Fun fibration の反変輸送は U の共変輸送との前合成。一般の評価や単一ファイバー同型に底辺に沿うこの作用がない。

:::

:::corollary "kerodon_5_3_6_11"
Kerodon Corollary 5.3.6.11（[Tag 0474](https://kerodon.net/tag/0474)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：片側が Kan・左ファイブレーション・反対と cartesian 判定・一点・写像の移送を照合。U の hQCat 値 homotopy transport と fiberwise Fun の反変輸送の両立。homotopyTransport の共変の合成だけでは指定 Fun との比較がない。

:::

:::lemma_ "kerodon_5_3_6_12" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_5_3_31, kerodon_4_5_6_14, kerodon_4_5_8_5, kerodon_5_1_1_1, kerodon_5_1_4_1, kerodon_5_1_4_9, kerodon_5_2_1_1, kerodon_5_3_2_12, kerodon_5_3_4_9, kerodon_5_3_6_5, kerodon_5_3_6_7")
Kerodon Lemma 5.3.6.12（[Tag 02UA](https://kerodon.net/tag/02UA)）。対応表の状態：なし。

fiberwiseHomPostcomp\_innerFibrationは射全体のinner性。原文は指定した辺eのV′-cartesian性であり、inner性はこの辺の結論の一部を直接与えない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.fiberwiseHomPostcomp_innerFibration`

:::

:::lemma_ "kerodon_5_3_6_13" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_5_3_31, kerodon_4_5_6_14, kerodon_5_1_1_1, kerodon_5_1_2_5, kerodon_5_1_4_1, kerodon_5_2_1_3, kerodon_5_2_2_8, kerodon_5_2_4_2, kerodon_5_3_6_7, kerodon_5_3_6_12")
Kerodon Lemma 5.3.6.13（[Tag 02UF](https://kerodon.net/tag/02UF)）。対応表の状態：なし。

引用はV′が両側の底への射影に対するcartesian辺を保つこと。原文はV′の指定辺への持ち上げの存在で、保存性と持ち上げは別の結論。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.fiberwiseHomPostcomp_preservesCartesianEdges`

:::

# 5.3.7 Application: Path Fibrations

%%%
number := false
tag := "kerodon-5-3-7"
%%%

Kerodon [Tag 01US](https://kerodon.net/tag/01US)

:::lemma_ "kerodon_5_3_7_1" (uses := "kerodon_1_1_0_6, kerodon_4_4_4_7")
Kerodon Lemma 5.3.7.1（[Tag 0475](https://kerodon.net/tag/0475)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：一点の coslice と矢印圏・相対関手と保存辺の部分圏・通常圏の pullback–pushforwardを照合。矢印 ∞ 圏で ev₀(e) の U-cocartesian 性から組になった評価射に対する V-cocartesian 性を得る主張。点評価の保存だけでは逆の向きの主張を与えない。

:::

:::proposition "kerodon_5_3_7_2" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_1_4_1, kerodon_5_1_1_1, kerodon_5_1_2_4, kerodon_5_1_4_1, kerodon_5_3_7_1")
Kerodon Proposition 5.3.7.2（[Tag 0477](https://kerodon.net/tag/0477)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：一点の coslice と矢印圏・相対関手と保存辺の部分圏・通常圏の pullback–pushforwardを照合。cocartesian fibration の四角が誘導する oriented fiber product の辺の性質。通常の pullback に対する保存は矢印対象の評価を含まない。

:::

:::corollary "kerodon_5_3_7_3" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_5_1_4_1, kerodon_5_3_7_2")
Kerodon Corollary 5.3.7.3（[Tag 0478](https://kerodon.net/tag/0478)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：一点の coslice と矢印圏・相対関手と保存辺の部分圏・通常圏の pullback–pushforwardを照合。向き付き引き戻しの二射影の fibration と、片側射影の cartesian 辺の判定。laxPullbackProjection の型には辺の判定がない。

:::

:::corollary "kerodon_5_3_7_4" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_4_5_1, kerodon_4_4_5_6, kerodon_4_5_3_33, kerodon_5_1_1_1, kerodon_5_1_4_1, kerodon_5_1_6_1, kerodon_5_3_7_2")
Kerodon Corollary 5.3.7.4（[Tag 06MA](https://kerodon.net/tag/06MA)）。対応表の状態：一部。

底C=Δ⁰に限ると原文の相対比較射Vは同じconeRestriction。cocartesianHornFibration\_coneRestrictionとhorn/cartesian条件の比較で同じfibration性を与え、apex可逆ならcocartesianという十分方向も直接ある。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianHornFibration_coneRestriction`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.hasCocartesianHornLifting_coneRestriction_of_apex`

:::

:::corollary "kerodon_5_3_7_5" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_5_1_1_11, kerodon_5_1_4_1, kerodon_5_3_7_4")
Kerodon Corollary 5.3.7.5（[Tag 02VW](https://kerodon.net/tag/02VW)）。対応表の状態：一部。

cocartesianHornFibration\_coneRestrictionは原文(1)のfibration性、hasCocartesianHornLifting\_coneRestriction\_of\_apexは辺の十分条件を直接与える。逆方向と(2)全体は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianHornFibration_coneRestriction`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.hasCocartesianHornLifting_coneRestriction_of_apex`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.coconeRestriction_hasLiftingProperty_finalVertex`

:::

:::proposition "kerodon_5_3_7_7"
Kerodon Proposition 5.3.7.7（[Tag 05PK](https://kerodon.net/tag/05PK)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：一点の coslice と矢印圏・相対関手と保存辺の部分圏・通常圏の pullback–pushforwardを照合。辺 f に沿う coslice 等の図式と共変輸送が作る四角の比較。join の前合成による制限だけでは transport と同定できない。

:::

:::theorem "kerodon_5_3_7_8"
Kerodon Theorem 5.3.7.8（[Tag 037Z](https://kerodon.net/tag/037Z)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：一点の coslice と矢印圏・相対関手と保存辺の部分圏・通常圏の pullback–pushforwardを照合。対角 δ の制限が、cocartesian 辺保存関手に対して自明 Kan ファイブレーション。相対 Fun の restriction 一般の型に保存部分圏がない。

:::

:::definition "kerodon_5_3_7_9"
Kerodon Notation 5.3.7.9（[Tag 02UH](https://kerodon.net/tag/02UH)）。対応表の状態：一部。

fiberwiseHomCurryにA=C、a=id、HをDへの第二射影として代入すれば、恒等Dをcurryした原文最初のsectionを直接構成し、projection補題が底上の等式を返す。Resのpullbackとcocartesian部分への制限全体は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomCurry`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomCurry_projection`

:::

:::proposition "kerodon_5_3_7_11"
Kerodon Proposition 5.3.7.11（[Tag 02UK](https://kerodon.net/tag/02UK)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：一点の coslice と矢印圏・相対関手と保存辺の部分圏・通常圏の pullback–pushforwardを照合。cocartesian V と cartesian U に対する Res の cocartesian 性とその辺の判定。通常の functor category の fibration の型に Res の保存条件がない。

:::

:::proposition "kerodon_5_3_7_12"
Kerodon Proposition 5.3.7.12（[Tag 02UL](https://kerodon.net/tag/02UL)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：一点の coslice と矢印圏・相対関手と保存辺の部分圏・通常圏の pullback–pushforwardを照合。Res の普遍性を cocartesian 辺を保存する両相対関手圏の比較として述べる結論。通常の pullback–pushforward 随伴の型はこの充満部分圏に制限しない。

:::

# 5.3.8 Digression: Minimal Fibrations

%%%
number := false
tag := "kerodon-5-3-8"
%%%

Kerodon [Tag 05PM](https://kerodon.net/tag/05PM)

:::definition "kerodon_5_3_8_1"
Kerodon Definition 5.3.8.1（[Tag 05PN](https://kerodon.net/tag/05PN)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Kan ファイブレーションの最小性・Δ¹・Δⁿ と最小模型・通常圏の骨格を照合。各 Δⁿ 上の pullback が minimal ∞ 圏である内ファイブレーションの述語。minimal Kan fibration の定義とは対象が異なる。

:::

:::proposition "kerodon_5_3_8_7"
Kerodon Proposition 5.3.8.7（[Tag 05PU](https://kerodon.net/tag/05PU)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Kan ファイブレーションの最小性・Δ¹・Δⁿ と最小模型・通常圏の骨格を照合。半順序で添字付けた minimal 値図式の weighted nerve の minimal 性。weighted nerve の内ファイブレーション性に minimality の結論がない。

:::

:::corollary "kerodon_5_3_8_8"
Kerodon Corollary 5.3.8.8（[Tag 05PV](https://kerodon.net/tag/05PV)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Kan ファイブレーションの最小性・Δ¹・Δⁿ と最小模型・通常圏の骨格を照合。任意の通常圏で添字付けた minimal 値図式の weighted nerve 射影の相対 minimal 性。半順序の nerve の薄さだけでは一般に及ばない。

:::

:::corollary "kerodon_5_3_8_9"
Kerodon Corollary 5.3.8.9（[Tag 05PW](https://kerodon.net/tag/05PW)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Kan ファイブレーションの最小性・Δ¹・Δⁿ と最小模型・通常圏の骨格を照合。Δⁿ 上の cocartesian fibration の全空間の minimal 性と最小な値を持つ表示等の同値。輸送の strictification は値の minimal 性を要求しない。

:::

:::corollary "kerodon_5_3_8_10"
Kerodon Corollary 5.3.8.10（[Tag 05PX](https://kerodon.net/tag/05PX)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Kan ファイブレーションの最小性・Δ¹・Δⁿ と最小模型・通常圏の骨格を照合。Kan fibration の二種の相対 minimality の同値。個別の minimal model の変形レトラクトからは各 Δⁿ 上の最小性の比較が出ない。

:::

:::proposition "kerodon_5_3_8_11" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_4_5_9, kerodon_4_5_2_12, kerodon_4_5_2_15")
Kerodon Proposition 5.3.8.11（[Tag 05PY](https://kerodon.net/tag/05PY)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Kan ファイブレーションの最小性・Δ¹・Δⁿ と最小模型・通常圏の骨格を照合。任意の内ファイブレーションに対して指定された minimal 部分複体とその比較を取る結果。minimal Kan 複体の構成では Kan の仮定が強い。

:::

