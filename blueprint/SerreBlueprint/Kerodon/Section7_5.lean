import Verso
import VersoManual
import VersoBlueprint
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.CocartesianSections
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.NerveCocartesianFibration
import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.WeakHomotopy
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.BousfieldKan
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.BousfieldKanHomotopyInvariance
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.BousfieldKanSectionsIso
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.GeneralReflectedCriterion
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.KanConeComparisonCriterion
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.SectionsKan
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedConeRestriction
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedFunctor

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "7.5 Homotopy Limits and Colimits" =>
%%%
number := false
tag := "kerodon-7-5"
%%%

Kerodon の 7.5 節（[Tag 039Y](https://kerodon.net/tag/039Y)）の項目と、SerrePositivity・Mathlib の宣言との対応。本文は対応表（research/kerodon-coverage）の判定の理由の要約で、Kerodon の本文の写しではない。

# 7.5.1 Homotopy Limits of Kan Complexes

%%%
number := false
tag := "kerodon-7-5-1"
%%%

Kerodon [Tag 039Z](https://kerodon.net/tag/039Z)

:::definition "kerodon_7_5_1_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanSectionsIso")
Kerodon Construction 7.5.1.1（[Tag 03A0](https://kerodon.net/tag/03A0)）。対応表の状態：本体にある。

仮定：小さい通常圏 I と H:I⥤SSet。定義は値の Kan 性を要求しない（Lean が弱い）。結論：bousfieldKanSectionsIso は holim と weightedNerveProjection H の単体的切断の同型（原文と一致）。

:::

:::proposition "kerodon_7_5_1_2" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim_kanComplex")
Kerodon Proposition 7.5.1.2（[Tag 03A1](https://kerodon.net/tag/03A1)）。対応表の状態：本体にある。

仮定：小さい通常圏 I と各値が KanComplex の H:I⥤SSet（Kerodon と一致）。結論：bousfieldKanHolim H が KanComplex（原文と一致）。

:::

:::proposition "kerodon_7_5_1_5"
Kerodon Proposition 7.5.1.5（[Tag 03A4](https://kerodon.net/tag/03A4)）。対応表の状態：なし。

標準unstraighteningの切断極限と、既存のstrict錐のBK比較による判定はあるが、BK holim自体を同じ図式のnative錐の頂点とする比較はこの引用にない。別の極限対象の存在だけでは数えない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentDiagramSectionsCone_isLimit`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.kanCone_isLimit_iff_bousfieldKanComparison`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanLimitComparison_homotopyEquivalence_of_extensions`

:::

# 7.5.2 Homotopy Limits of ∞-Categories

%%%
number := false
tag := "kerodon-7-5-2"
%%%

Kerodon [Tag 03A7](https://kerodon.net/tag/03A7)

:::definition "kerodon_7_5_2_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanSectionsIso, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianSections, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianSections_quasicategory, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection_cocartesianFibration")
Kerodon Construction 7.5.2.1（[Tag 03A8](https://kerodon.net/tag/03A8)）。対応表の状態：本体にある。

cocartesianSectionsを同じweightedNerveProjection Fと底の恒等射へ適用すれば、原文の全切断中のcocartesian関手を張る全部分準圏をそのまま構成できる。BKの全切断空間とは区別し、実際の構成の宣言を追記した。

:::

:::definition "kerodon_7_5_2_4"
Kerodon Variant 7.5.2.4（[Tag 03Y3](https://kerodon.net/tag/03Y3)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：全切断の BK 同型と cocartesian 切断の準圏はある。通常圏の Grothendieck 構成の cocartesian 切断圏の nerve との指定同型は見つからない。

:::

:::proposition "kerodon_7_5_2_6"
Kerodon Proposition 7.5.2.6（[Tag 03AB](https://kerodon.net/tag/03AB)）。対応表の状態：一部。

weightedNerveProjection\_cocartesianFibrationとcocartesianSections\_quasicategoryは原文の同じholimが準圏であるという前半を直接返す。QC内の極限性という後半はSpace内の極限性で代用しない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentDiagramSectionsCone_isLimit`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianSections`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianSections_quasicategory`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection_cocartesianFibration`

:::

:::proposition "kerodon_7_5_2_13" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_7_3_22")
Kerodon Proposition 7.5.2.13（[Tag 03AJ](https://kerodon.net/tag/03AJ)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：切断の始頂点評価が自明 Kan になる。BK 比較が離散添字で同型になる型もある。任意の始対象つき添字圏で通常極限から cocartesian 切断への指定包含を同値とする型は見つからない。

:::

# 7.5.3 The Homotopy Limit as a Derived Functor

%%%
number := false
tag := "kerodon-7-5-3"
%%%

Kerodon [Tag 03AP](https://kerodon.net/tag/03AP)

:::proposition "kerodon_7_5_3_1" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_5_6_1, kerodon_5_3_1_1, kerodon_5_3_2_18, kerodon_5_3_2_22")
Kerodon Proposition 7.5.3.1（[Tag 03AQ](https://kerodon.net/tag/03AQ)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：固定形状の底上の関手空間の準圏性はある。C の全対象に対する弱輸送図式全体が injective な持ち上げ性を満たす型は見つからない。

:::

:::corollary "kerodon_7_5_3_2" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_5_1_4_1, kerodon_5_3_1_5, kerodon_7_5_3_1")
Kerodon Corollary 7.5.3.2（[Tag 03AR](https://kerodon.net/tag/03AR)）。対応表の状態：なし。

cocartesianStrictTransportDiagramの定義は図式を構成するだけで、原文のisofibrantという持ち上げ結論を含まない。構成が存在することはこの系の結論の成分ではない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransportDiagram`

:::

:::definition "kerodon_7_5_3_3" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_5_3_3_1, kerodon_5_3_4_7, kerodon_5_3_4_11")
Kerodon Construction 7.5.3.3（[Tag 03AS](https://kerodon.net/tag/03AS)）。対応表の状態：一部。

FをKan値に限るとweightedTransportUnitは同じweighted nerveの全切断によるstrict transportへの自然変換αを構成する。left fibrationでは全切断がcocartesianなので原文の構成のα成分に一致する。universal/taut scaffoldとの可換性と一意性は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedTransportUnit`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.kanCocartesianSectionsι_isIso_of_leftFibration`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanSectionsIso`

:::

:::proposition "kerodon_7_5_3_4" (uses := "kerodon_1_4_0_1, kerodon_5_3_1_7, kerodon_7_5_3_2, kerodon_7_5_3_3")
Kerodon Proposition 7.5.3.4（[Tag 03AT](https://kerodon.net/tag/03AT)）。対応表の状態：一部。

FをKan値に限ればweightedTransportUnitComponent\_isQCatEquivalenceは同じαの各成分の圏同値性を直接返す。全図式のisofibrant性とαのmono性は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedTransportUnitComponent_isQCatEquivalence`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.kanCocartesianSectionsι_isIso_of_leftFibration`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanSectionsIso`

:::

:::corollary "kerodon_7_5_3_5"
Kerodon Corollary 7.5.3.5（[Tag 03AU](https://kerodon.net/tag/03AU)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Kan 値の unit の成分ごとの圏同値はある。任意の単体集合値図式から QCat 値の isofibrant 図式への単射を作る型は見つからない。

:::

:::definition "kerodon_7_5_3_6"
Kerodon Variant 7.5.3.6（[Tag 03AV](https://kerodon.net/tag/03AV)）。対応表の状態：一部。

functorialなcontinuousKanReplacementとその単位をFに後合成すると、anodyne単位のmono性と弱同値性から、同じFからKan値図式へのlevelwise単射弱同値を直接得る。図式全体のisofibrant性は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit_anodyne`、`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.continuousKanReplacementUnit_isWeakHomotopyEquivalence`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement`

:::

:::proposition "kerodon_7_5_3_7" (uses := "kerodon_1_1_0_6, kerodon_7_5_3_3, kerodon_7_5_3_10")
Kerodon Proposition 7.5.3.7（[Tag 03AW](https://kerodon.net/tag/03AW)）。対応表の状態：なし。

引用のlim→BK holimのホモトピー同値は、原文のholim Fとlim F⁺の指定された単体集合の厳密同型θではない。弱い同値を厳密同型の成分とは数えない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanLimitComparison_homotopyEquivalence_of_extensions`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeComparison_cospan_homotopyEquivalence`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanLimitComparison_tower_homotopyEquivalence`

:::

:::lemma_ "kerodon_7_5_3_8"
Kerodon Lemma 7.5.3.8（[Tag 03AX](https://kerodon.net/tag/03AX)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：輸送の単体添字 nerve 関手の余極限保存はある。Cᵒᵖ にわたる各 C\_\{c/\} の nerve を C の nerve へ射影する指定余錐の余極限性は見つからない。

:::

:::definition "kerodon_7_5_3_10" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_5_1_4_1, kerodon_5_3_1_5")
Kerodon Variant 7.5.3.10（[Tag 03AZ](https://kerodon.net/tag/03AZ)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：全切断の BK end 同型と左ファイブレーションの strict transport 図式はある。任意の cocartesian fibration で cocartesian 切断へ制限した strict limit との同型は見つからない。

:::

:::proposition "kerodon_7_5_3_12" (uses := "kerodon_1_4_0_1, kerodon_4_5_7_17, kerodon_7_5_3_3, kerodon_7_5_3_4, kerodon_7_5_3_7")
Kerodon Proposition 7.5.3.12（[Tag 03B1](https://kerodon.net/tag/03B1)）。対応表の状態：一部。

FをKan値で全levelwise anodyneの図式からの延長条件も満たすと強めると、bousfieldKanLimitComparison\_homotopyEquivalence\_of\_extensionsは同じlim F→holim Fの比較の同値を返す。BKの全切断とcocartesian切断はleft fibrationの場合の同型で比較する。一般QCat値は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanLimitComparison_homotopyEquivalence_of_extensions`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanMap_isQCatEquivalence`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeComparison_cospan_homotopyEquivalence`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanLimitComparison_tower_homotopyEquivalence`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.kanCocartesianSectionsι_isIso_of_leftFibration`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanSectionsIso`

:::

# 7.5.4 Homotopy Limit Diagrams

%%%
number := false
tag := "kerodon-7-5-4"
%%%

Kerodon [Tag 03B5](https://kerodon.net/tag/03B5)

:::definition "kerodon_7_5_4_1" (uses := "kerodon_1_2_5_1")
Kerodon Definition 7.5.4.1（[Tag 03B6](https://kerodon.net/tag/03B6)）。対応表の状態：一部。

bousfieldKanConeComparisonは同じ増強図式の頂点→lim→BK holimという合成射を直接構成し、そのIsSimplicialHomotopyEquivalenceを条件とすることで原文のKan値の定義を表す。KSTの基点付きπ\_\*版は根拠としない。専用述語名の欠如は不足にしない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeComparison`、`SerrePositivity.KST.Descent.Main.HasHomotopyLimitDescent`

:::

:::proposition "kerodon_7_5_4_4" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanMap_homotopyEquivalence, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeComparison_naturality, SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence.comp, SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence.cancel_left, SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence.cancel_right") (uses := "kerodon_1_2_5_1")
Kerodon Proposition 7.5.4.4（[Tag 03B9](https://kerodon.net/tag/03B9)）。対応表の状態：本体にある。

weightedConeComparison\_naturalityが同じ増強自然変換の比較四角の可換性を与え、bousfieldKanMap\_homotopyEquivalenceが右辺を同値にする。Kan複体の弱同値との同値およびcomp/cancel\_left/cancel\_rightをこの四角へ適用すると原文の三条件の二つから三つを直接得る。

:::

:::proposition "kerodon_7_5_4_5" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.kanCone_isLimit_iff_bousfieldKanComparison")
Kerodon Proposition 7.5.4.5（[Tag 03BA](https://kerodon.net/tag/03BA)）。対応表の状態：本体にある。

仮定：小さい I、F:I⥤KanObject と通常圏の錐 c（Kerodon の増強図式と一致）。結論：strictCoherentCone c の極限性と、忘却した錐から BK holim への比較射の弱ホモトピー同値の iff（原文と一致）。

:::

:::corollary "kerodon_7_5_4_6" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone_isLimit_iff_reflectedStrictConeSectionsComparison, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone_isLimit_iff_reflectedRepresentableComparison")
Kerodon Corollary 7.5.4.6（[Tag 03BB](https://kerodon.net/tag/03BB)）。対応表の状態：本体にある。

仮定：小さい I、局所 Kan の単体豊穣圏、F:I⥤C とその通常圏の錐 c（Kerodon と一致）。結論：coherent nerve の錐の極限性と、各 x について表現可能写像空間の比較がホモトピー同値であることの iff（原文と一致）。

:::

:::corollary "kerodon_7_5_4_7"
Kerodon Corollary 7.5.4.7（[Tag 03BC](https://kerodon.net/tag/03BC)）。対応表の状態：一部。

全levelwise anodyneに対する延長条件を加えると、strict極限のBK比較同値とkanCone\_isLimit\_iff\_bousfieldKanComparisonは同じKan値の極限錐がSpace内でも極限と直接返す。isofibrantだけから延長条件を得たとはしない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanLimitComparison_homotopyEquivalence_of_extensions`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.kanCone_isLimit_iff_bousfieldKanComparison`

:::

:::definition "kerodon_7_5_4_8" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_7_5_4_1")
Kerodon Definition 7.5.4.8（[Tag 03BD](https://kerodon.net/tag/03BD)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Kan 値の指定錐の比較型と単体集合の弱同値な Kan 置換はある。任意の増強図式について、指定条件を満たす Kan 値増強図式への弱同値の存在を述語にした定義は見つからない。

:::

:::proposition "kerodon_7_5_4_10" (uses := "kerodon_1_1_0_6, kerodon_3_1_8_1, kerodon_3_4_2_10, kerodon_3_4_2_11, kerodon_7_5_4_4")
Kerodon Proposition 7.5.4.10（[Tag 03BF](https://kerodon.net/tag/03BF)）。対応表の状態：なし。

Kan値図式間のBK endの同値不変性だけでは、任意の単体集合値の別々のKan置換を比較する射が得られない。原文(1)⇒(2)の全置換に対する主張への比較が必要。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanMap_isQCatEquivalence`

:::

:::corollary "kerodon_7_5_4_11" (uses := "kerodon_3_1_8_1, kerodon_7_5_4_4, kerodon_7_5_4_10")
Kerodon Corollary 7.5.4.11（[Tag 03BG](https://kerodon.net/tag/03BG)）。対応表の状態：一部。

両増強図式をKan値に限ると、BK比較の自然性と成分弱同値の不変性、Kan複体の弱同値の二つから三つにより、同じ三条件の判定を直接得る。任意の単体集合値の置換比較は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanMap_isQCatEquivalence`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeComparison_naturality`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanMap_homotopyEquivalence`、`SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence.comp`、`SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence.cancel_left`、`SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence.cancel_right`

:::

:::corollary "kerodon_7_5_4_12" (uses := "kerodon_1_1_0_6, kerodon_1_2_3_1, kerodon_3_6_4_1, kerodon_7_5_4_11")
Kerodon Corollary 7.5.4.12（[Tag 03BH](https://kerodon.net/tag/03BH)）。対応表の状態：一部。

増強図式をKan値に限ると、現本体のbousfieldKanConeComparison\_reflection\_general\_iffは同じ錐と反対錐のhomotopy limit条件のiffを直接返す。古いreflection\_iffにあったstrict極限のKan性・lim比較同値の仮定は不要になっている。任意の単体集合値は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeComparison_reflection_iff`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeComparison_reflection_general_iff`

:::

:::proposition "kerodon_7_5_4_13" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_3_1_8_1, kerodon_3_4_0_3, kerodon_3_4_1_1, kerodon_3_4_1_6, kerodon_3_4_1_13, kerodon_7_5_4_8, kerodon_7_5_4_11")
Kerodon Proposition 7.5.4.13（[Tag 03BJ](https://kerodon.net/tag/03BJ)）。対応表の状態：一部。

四対象をKan複体に限るとkanCommSqCone\_isLimitとkanCone\_isLimit\_iff\_bousfieldKanComparisonは、同じ可換正方形がhomotopy pullbackならhomotopy limit diagramという向きを直接与える。逆向きと任意の単体集合は含まない。

宣言：`SerrePositivity.KST.Comparison.IsHomotopyPullback`、`SerrePositivity.KST.Fibration.kanCommSqCone_isLimit`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeComparison_cospan_homotopyEquivalence`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.kanCone_isLimit_iff_bousfieldKanComparison`

:::

# 7.5.5 Categorical Limit Diagrams

%%%
number := false
tag := "kerodon-7-5-5"
%%%

Kerodon [Tag 03BL](https://kerodon.net/tag/03BL)

:::definition "kerodon_7_5_5_1" (uses := "kerodon_1_4_0_1")
Kerodon Definition 7.5.5.1（[Tag 03BM](https://kerodon.net/tag/03BM)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：BK end への通常極限の比較と join 錐の極限性の述語は別々にある。QCat 値で cocartesian 切断へ至る指定合成の準圏同値を条件にした定義は見つからない。

:::

:::proposition "kerodon_7_5_5_7" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_4_5_1_16, kerodon_4_8_4_6, kerodon_7_5_5_1")
Kerodon Proposition 7.5.5.7（[Tag 03BT](https://kerodon.net/tag/03BT)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：∞圏の極限錐は全頂点の Hom 比較で判定できる。QCat 値の通常圏添字の増強図式で、全 K の core の条件を Δ¹ だけで検査する型は見つからない。

:::

:::corollary "kerodon_7_5_5_8" (uses := "kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_7_1_3_4, kerodon_7_5_4_6, kerodon_7_5_5_7")
Kerodon Corollary 7.5.5.8（[Tag 03BU](https://kerodon.net/tag/03BU)）。対応表の状態：なし。

指定pullback錐のQC内の極限性は、原文の同じ錐がcategorical limit diagramであるという述語と比較する型ではない。片方の別の極限性だけではiffの向きと数えない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.qCatPullbackInfinityCone_isLimit`

:::

:::corollary "kerodon_7_5_5_9"
Kerodon Corollary 7.5.5.9（[Tag 03BV](https://kerodon.net/tag/03BV)）。対応表の状態：一部。

形状をcospanで一脚がEquivalenceLiftingな図式に限ると、qCatPullbackInfinityCone\_isLimitは通常のstrict pullback錐がQC内で極限と直接返す。原文の存在と保存のこの形状の場合に一致し、一般形状は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.qCatPullbackInfinityCone_isLimit`

:::

:::corollary "kerodon_7_5_5_10" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_4_5_3_8, kerodon_4_5_3_15, kerodon_7_5_4_13, kerodon_7_5_5_1, kerodon_7_5_5_7")
Kerodon Corollary 7.5.5.10（[Tag 03BW](https://kerodon.net/tag/03BW)）。対応表の状態：なし。

catPullbackCone\_isLimitはQC内での極限性。原文(2)のcategorical limit diagramという指定の比較射条件との型の比較を欠き、別の極限述語への結論だけは数えない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.catPullbackCone_isLimit`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.qCatPullbackInfinityCone_isLimit`

:::

:::definition "kerodon_7_5_5_11"
Kerodon Definition 7.5.5.11（[Tag 03BY](https://kerodon.net/tag/03BY)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：join 錐の極限述語と単体写像の前合成同値はある。QCat 値の categorical limit 図式への成分同値の存在を条件とする単体集合値図式の定義は見つからない。

:::

:::proposition "kerodon_7_5_5_13" (uses := "kerodon_1_1_0_6, kerodon_4_1_3_2, kerodon_4_5_5_10, kerodon_4_5_5_11, kerodon_7_5_4_10")
Kerodon Proposition 7.5.5.13（[Tag 03C0](https://kerodon.net/tag/03C0)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：BK end の成分同値不変性は Kan 値の両図式を仮定する。一般の QCat 値への任意の置換に categorical limit 性が移る iff は見つからない。

:::

:::corollary "kerodon_7_5_5_14" (uses := "kerodon_1_1_0_6, kerodon_4_1_3_2, kerodon_7_5_5_13")
Kerodon Corollary 7.5.5.14（[Tag 03C1](https://kerodon.net/tag/03C1)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Kan 値の成分同値から BK end の同値を得る。一般の単体集合値の増強図式で categorical limit 性二つと頂点の categorical equivalence の三条件を比較する型は見つからない。

:::

:::corollary "kerodon_7_5_5_15" (uses := "kerodon_4_1_3_2, kerodon_7_5_4_12, kerodon_7_5_5_7, kerodon_7_5_5_14")
Kerodon Corollary 7.5.5.15（[Tag 03C2](https://kerodon.net/tag/03C2)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：準圏間の一射の同値は反対にしても同値。増強図式を各値で反対にした categorical limit 性との iff は見つからない。

:::

# 7.5.6 The Homotopy Colimit as a Derived Functor

%%%
number := false
tag := "kerodon-7-5-6"
%%%

Kerodon [Tag 03C3](https://kerodon.net/tag/03C3)

:::definition "kerodon_7_5_6_1" (uses := "kerodon_1_1_0_6")
Kerodon Definition 7.5.6.1（[Tag 03C4](https://kerodon.net/tag/03C4)）。対応表の状態：なし。

一般モデル圏のProjective.modelCategoryとisCofibrant\_objは、単体集合図式にlevelwise trivial Kan fibrationを使う原文の持ち上げ定義と比較する型を含まない。SSetの具体的モデル構造のinstanceもない。

宣言：`SerrePositivity.DiagramModel.Projective.modelCategory`、`SerrePositivity.DiagramModel.Projective.isCofibrant_obj`

:::

:::proposition "kerodon_7_5_6_7"
Kerodon Proposition 7.5.6.7（[Tag 03CB](https://kerodon.net/tag/03CB)）。対応表の状態：なし。

引用のmap\_weakEquivalenceはモデル圏で置換して作ったhocolim functorのmapについてで、原文の同じ通常colim(α)ではない。SSetの具体的モデル構造とその弱同値の同定もなく、類似だけでは数えない。

宣言：`SerrePositivity.DiagramModel.HomotopyColimit.map_weakEquivalence`、`SerrePositivity.DiagramModel.HomotopyColimit.comparison_weakEquivalence_of_cofibrant`

:::

:::definition "kerodon_7_5_6_8"
Kerodon Construction 7.5.6.8（[Tag 03CC](https://kerodon.net/tag/03CC)）。対応表の状態：なし。

BK coendの定義と一般モデル圏のreplacementは、原文のN(C\_/c)との指定pullbackによるF₊ではない。その自然変換を同定する比較がない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanColimit`、`SerrePositivity.DiagramModel.HomotopyColimit.replacement`

:::

:::proposition "kerodon_7_5_6_9"
Kerodon Proposition 7.5.6.9（[Tag 03CD](https://kerodon.net/tag/03CD)）。対応表の状態：なし。

一般モデル圏のreplacementのcofibrant性は原文の指定F₊の性質ではない。同じ図式との比較なしにcofibrantという語の一致は数えない。

宣言：`SerrePositivity.DiagramModel.HomotopyColimit.replacement_isCofibrant`

:::

:::proposition "kerodon_7_5_6_12"
Kerodon Proposition 7.5.6.12（[Tag 03CG](https://kerodon.net/tag/03CG)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：重みつきテンソルの coend を余極限にする型はある。N(C\_\{/c\}) による全空間の引き戻しの余極限から元の holim への指定同型と射影による特徴付けは見つからない。

:::

:::corollary "kerodon_7_5_6_14"
Kerodon Corollary 7.5.6.14（[Tag 03CJ](https://kerodon.net/tag/03CJ)）。対応表の状態：なし。

comparison\_weakEquivalence\_of\_cofibrantのcomparisonはモデル置換由来のhocolimからcolimへの射。原文のBK coend由来の比較と同じ射とする比較がない。

宣言：`SerrePositivity.DiagramModel.HomotopyColimit.comparison_weakEquivalence_of_cofibrant`

:::

# 7.5.7 Homotopy Colimit Diagrams

%%%
number := false
tag := "kerodon-7-5-7"
%%%

Kerodon [Tag 03CM](https://kerodon.net/tag/03CM)

:::proposition "kerodon_7_5_7_1"
Kerodon Proposition 7.5.7.1（[Tag 03CN](https://kerodon.net/tag/03CN)）。対応表の状態：一部。

XをKan置換したBK coend（kanReflectedBousfieldKanColimitObject F）に指定すると、bousfieldKanCoherentCocone\_isColimitとそのvertex計算は同じXが余極限と直接返す。一般Xのiffは含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.bousfieldKanCoherentCocone_isColimit`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.kanDiagramCoherentNerve_hasColimit`、`SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.bousfieldKanCoherentCocone_vertex`

:::

:::definition "kerodon_7_5_7_3" (uses := "kerodon_1_1_0_6")
Kerodon Definition 7.5.7.3（[Tag 03CQ](https://kerodon.net/tag/03CQ)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：BK coend と単体写像の弱ホモトピー同値は定義される。指定増強図式で coend から通常余極限を経て頂点へ至る合成を弱同値とする述語は見つからない。

:::

:::proposition "kerodon_7_5_7_5"
Kerodon Proposition 7.5.7.5（[Tag 03CS](https://kerodon.net/tag/03CS)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：フィルター付き通常余極限は成分ごとの弱ホモトピー同値を保つ。一般の BK 余極限図式と頂点の弱同値を含む三条件の判定は見つからない。

:::

:::proposition "kerodon_7_5_7_6"
Kerodon Proposition 7.5.7.6（[Tag 03CT](https://kerodon.net/tag/03CT)）。対応表の状態：なし。

引用はnativeなcoherent余錐の余極限性と反変表現可能比較を判定する。原文は任意の単体集合値の増強図式のhomotopy colimit条件であり、そのBK比較射との同定を型に含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictNativeCocone_isColimit_iff_reflectedRepresentableComparison`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCocone_isColimit_iff`

:::

:::corollary "kerodon_7_5_7_7"
Kerodon Corollary 7.5.7.7（[Tag 03CU](https://kerodon.net/tag/03CU)）。対応表の状態：なし。

strict coherent余錐の反変Homによる判定は、原文のBK coendから頂点への指定比較射の弱同値という条件への比較を含まない。専用述語名の有無でなく、この射の同定が不足。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictNativeCocone_isColimit_iff_reflectedRepresentableComparison`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCocone_isColimit_iff`

:::

:::corollary "kerodon_7_5_7_8"
Kerodon Corollary 7.5.7.8（[Tag 03CV](https://kerodon.net/tag/03CV)）。対応表の状態：なし。

weightedColimitOppositeIsoは重みWも反転する。原文はBKの同じ重みを用いたFとFᵒᵖの増強図式の判定であり、反転した重みを元の重みに戻し頂点への指定射と可換とする比較がない。

宣言：`SerrePositivity.InfinityCategories.Project.FilteredExchange.WeightedColimitOpposite.weightedColimitOppositeIso`、`SerrePositivity.InfinityCategories.Project.FilteredExchange.opposite_map_isWeakHomotopyEquivalence`

:::

:::corollary "kerodon_7_5_7_9"
Kerodon Corollary 7.5.7.9（[Tag 03CW](https://kerodon.net/tag/03CW)）。対応表の状態：なし。

標準spanのSpace内での余極限性は原文のhomotopy colimit diagramというBK比較射の弱同値性ではない。その比較がなく、同じ語の極限性で代用しない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.spaceHomotopyPushoutCocone_isColimitCone`

:::

# 7.5.8 Categorical Colimit Diagrams

%%%
number := false
tag := "kerodon-7-5-8"
%%%

Kerodon [Tag 03CY](https://kerodon.net/tag/03CY)

:::proposition "kerodon_7_5_8_1"
Kerodon Proposition 7.5.8.1（[Tag 03CZ](https://kerodon.net/tag/03CZ)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：辺の局所化と空間値の全空間余極限はある。QCat 値の BK 全空間の横辺を局所化して coherent nerve 図式の余極限となる iff は見つからない。

:::

:::definition "kerodon_7_5_8_2" (uses := "kerodon_1_1_0_6, kerodon_5_3_4_1, kerodon_6_3_1_9")
Kerodon Definition 7.5.8.2（[Tag 03D0](https://kerodon.net/tag/03D0)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：局所化と BK coend は別々に定義される。通常余極限を経る指定合成が全横辺の局所化となる条件を増強図式の述語にした定義は見つからない。

:::

:::proposition "kerodon_7_5_8_4" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_6_3_1_13, kerodon_7_5_4_1, kerodon_7_5_5_1, kerodon_7_5_5_15")
Kerodon Proposition 7.5.8.4（[Tag 03D2](https://kerodon.net/tag/03D2)）。対応表の状態：なし。

BK coendとHomの随伴同型だけでは、原文のcategorical colimitの横辺反転による指定比較に接続しない。Kan値の別の比較同値も全QCat標的の同じ条件を直接返さない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanColimitHomIso`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.kanBousfieldKanColimitHomComparison_homotopyEquivalence`

:::

:::corollary "kerodon_7_5_8_5" (uses := "kerodon_1_1_0_6, kerodon_4_5_5_1, kerodon_7_5_8_2")
Kerodon Corollary 7.5.8.5（[Tag 03D3](https://kerodon.net/tag/03D3)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：空間圏の指定 span 余錐の余極限性と局所化の述語はある。任意の正方形で categorical pushout と横辺局所化による categorical colimit を比較する型は見つからない。

:::

:::corollary "kerodon_7_5_8_6" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_5_4_8, kerodon_7_5_8_4")
Kerodon Corollary 7.5.8.6（[Tag 03D5](https://kerodon.net/tag/03D5)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：同一図式上の二つの余錐の関手同型で余極限性を移す。任意の単体集合値増強図式の成分同値の下で categorical colimit 性と頂点同値の三条件を比較する型は見つからない。

:::

:::corollary "kerodon_7_5_8_7" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_4_5_7_22, kerodon_7_5_6_1, kerodon_7_5_8_4")
Kerodon Corollary 7.5.8.7（[Tag 03D6](https://kerodon.net/tag/03D6)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常の coend 余極限の型はある。projective cofibrancy を仮定して通常の余極限余錐を横辺局所化による categorical colimit と判定する型は見つからない。

:::

:::corollary "kerodon_7_5_8_8"
Kerodon Corollary 7.5.8.8（[Tag 03D7](https://kerodon.net/tag/03D7)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：重みつき余極限の関手と局所化の述語を確認した。projective cofibrant な F の BK coend から通常余極限への射が横辺の局所化を与える型は見つからない。

:::

:::corollary "kerodon_7_5_8_9" (uses := "kerodon_1_4_0_1, kerodon_7_1_3_5, kerodon_7_5_4_6, kerodon_7_5_7_3, kerodon_7_5_8_4")
Kerodon Corollary 7.5.8.9（[Tag 03D8](https://kerodon.net/tag/03D8)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Kan 値の coherent な反対圏側の BK 錐が極限となる型はある。一般の QCat 値の増強図式と CatInfinity の余極限性を比較する iff は見つからない。

:::

:::corollary "kerodon_7_5_8_10"
Kerodon Corollary 7.5.8.10（[Tag 03D9](https://kerodon.net/tag/03D9)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Kan 複体間の射では弱ホモトピー同値と準圏同値を比較できる。横辺の局所化と BK 全空間から頂点への弱同値で定める二種類の余極限図式の iff は見つからない。

:::

:::corollary "kerodon_7_5_8_11"
Kerodon Corollary 7.5.8.11（[Tag 03DA](https://kerodon.net/tag/03DA)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：個別の準圏同値の反対化と重みつき余極限の反対化の同型はある。反対図式の横辺の局所化を含む categorical colimit 性の iff は見つからない。

:::

:::proposition "kerodon_7_5_8_12"
Kerodon Proposition 7.5.8.12（[Tag 03DB](https://kerodon.net/tag/03DB)）。対応表の状態：なし。

MathlibのGrothendieck圏のfiberwiseColimitは通常圏値の図式。原文の任意のcategorical colimit単体集合Kとその上の同じqに対するQへの比較がない。

宣言：`CategoryTheory.Limits.fiberwiseColimit`、`CategoryTheory.Limits.colimitFiberwiseColimitIso`

:::

:::corollary "kerodon_7_5_8_13" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1")
Kerodon Corollary 7.5.8.13（[Tag 03DC](https://kerodon.net/tag/03DC)）。対応表の状態：なし。

通常圏のGrothendieck形状の余極限存在は、原文の指定categorical colimit K形状への∞圏の余極限と比較する型を持たない。

宣言：`CategoryTheory.Limits.hasColimitsOfShape_grothendieck`

:::

