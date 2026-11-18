import Verso
import VersoManual
import VersoBlueprint
import Mathlib.AlgebraicTopology.SimplicialSet.Nonsingular
import Mathlib.CategoryTheory.Localization.Predicate
import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InverseAttachmentUniversal
import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Localization
import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LocalizationResolution
import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Saturation

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "6.3 Localization" =>
%%%
number := false
tag := "kerodon-6-3"
%%%

Kerodon の 6.3 節（[Tag 01M4](https://kerodon.net/tag/01M4)）の項目と、SerrePositivity・Mathlib の宣言との対応。本文は対応表（research/kerodon-coverage）の判定の理由の要約で、Kerodon の本文の写しではない。

:::definition "kerodon_6_3_0_1" (lean := "CategoryTheory.Localization.StrictUniversalPropertyFixedTarget")
Kerodon Definition 6.3.0.1（[Tag 01M5](https://kerodon.net/tag/01M5)）。対応表の状態：Mathlib にある。

仮定：通常の圏の関手 F:C→D、反転する射のクラス W、任意の試験圏 E（Lean は E を引数に取る）（Kerodon と一致）。結論：StrictUniversalPropertyFixedTarget は W を反転する各関手の厳密な因子化と一意性。任意の E について取れば原文の全単射（一致）。

:::

:::definition "kerodon_6_3_0_6"
Kerodon Definition 6.3.0.6（[Tag 01M9](https://kerodon.net/tag/01M9)）。対応表の状態：一部。

MathlibのFunctor.IsLocalizationからfull\_whiskeringLeftおよびfaithfulの既存instanceにより、原文の全試験圏への前合成の充満忠実性を直接得る。本質的像の全判定と普遍性からの逆は含まない。

宣言：`CategoryTheory.Functor.IsLocalization`、`CategoryTheory.Localization.full_whiskeringLeft`

:::

# 6.3.1 Localizations of ∞-Categories

%%%
number := false
tag := "kerodon-6-3-1"
%%%

Kerodon [Tag 01ME](https://kerodon.net/tag/01ME)

:::definition "kerodon_6_3_1_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertingFunctors, SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertingFunctors_quasicategory")
Kerodon Notation 6.3.1.1（[Tag 01MF](https://kerodon.net/tag/01MF)）。対応表の状態：本体にある。

仮定：単体集合 X、試験 ∞ 圏 E、X の辺の族 W（Lean が弱い：構成自体は E の ∞ 圏性を要しない）。結論：invertingFunctors X E W は W を可逆辺に送る関手を頂点とする Fun(X,E) の全部分複体（一致）。

:::

:::definition "kerodon_6_3_1_9" (lean := "SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization, SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.localizationPrecomposition")
Kerodon Definition 6.3.1.9（[Tag 01MP](https://kerodon.net/tag/01MP)）。対応表の状態：本体にある。

仮定：単体集合の射 F:X→D、辺の族 W、同一宇宙の試験 ∞ 圏 E（Kerodon と一致）。結論：F が W を反転し、Fun(D,E)→invertingFunctors X E W が圏同値。原文の充満忠実性と指定本質像に対応（一致）。

:::

:::proposition "kerodon_6_3_1_13" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_4_8_4_4, kerodon_6_3_1_9")
Kerodon Proposition 6.3.1.13（[Tag 01MS](https://kerodon.net/tag/01MS)）。対応表の状態：一部。

IsLocalizationは同じFの全準圏への指定localizationPrecompositionの同値性、すなわち原文(2)を直接条件にする。(3),(4)のcoreのπ₀からの逆を含む四条件のiffは含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization`、`SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UniversalConsequences.IsLocalization.precomposition_isFullyFaithful`、`SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UniversalConsequences.IsLocalization.exists_extension`、`SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.isLocalization_of_fullyFaithful_extensions`

:::

:::proposition "kerodon_6_3_1_21" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_3_1_8_2, kerodon_4_4_3_23, kerodon_6_3_1_13")
Kerodon Proposition 6.3.1.21（[Tag 01MY](https://kerodon.net/tag/01MY)）。対応表の状態：一部。

localization\_all\_isKanは同じFの全辺の局所化から原文の標的DのKan性を直接返す。Fの弱ホモトピー同値と逆方向は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.localization_all_isKan`、`SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.groupoidCompletion_isLocalization`、`SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertsAllEdges_toKan`

:::

:::proposition "kerodon_6_3_1_22"
Kerodon Proposition 6.3.1.22（[Tag 02LS](https://kerodon.net/tag/02LS)）。対応表の状態：一部。

W′=∅、F′を前合成同値に限るとlocalization\_postcomp\_precompositionEquivalenceは同じ合成F≫F′がW=W∪∅の局所化になると直接返す。一般の第二の辺集合の局所化ではない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.localization_postcomp_precompositionEquivalence`、`SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.isLocalization_of_weakDeformation`

:::

:::corollary "kerodon_6_3_1_23" (lean := "SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization.of_subset_invertedEdges")
Kerodon Corollary 6.3.1.23（[Tag 02LT](https://kerodon.net/tag/02LT)）。対応表の状態：本体にある。

仮定：W で局所化する F と追加の辺の族（Lean が弱い：像が退化でなく可逆ならよい）。結論：W と追加の辺の和集合に対しても IsLocalization（一致）。

:::

# 6.3.2 Existence of Localizations

%%%
number := false
tag := "kerodon-6-3-2"
%%%

Kerodon [Tag 01MZ](https://kerodon.net/tag/01MZ)

:::proposition "kerodon_6_3_2_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.exists_quasicategory_localization, SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.inverseAttachment_isLocalization")
Kerodon Proposition 6.3.2.1（[Tag 01N0](https://kerodon.net/tag/01N0)）。対応表の状態：本体にある。

仮定：単体集合 X と任意の辺の族 W（Kerodon と一致）。結論：Quasicategory Q と IsLocalization F W を満たす F:X→Q が存在（一致）。

:::

:::proposition "kerodon_6_3_2_4" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_5_3_19, kerodon_4_5_3_22, kerodon_4_5_3_28")
Kerodon Proposition 6.3.2.4（[Tag 05ZD](https://kerodon.net/tag/05ZD)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：上辺が局所化の四角で categorical pushout と下辺が像の辺を反転する局所化との同値。初頂点射の strict pushout の閉性は指定射の特別な場合。

:::

:::corollary "kerodon_6_3_2_5" (uses := "kerodon_1_1_0_6, kerodon_6_3_2_4")
Kerodon Corollary 6.3.2.5（[Tag 05ZG](https://kerodon.net/tag/05ZG)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：互いに重ならない指定辺を Δ⁰ へ潰す商の局所化性。inverseAttachment は各辺に walking equivalence を貼る別の pushout。

:::

:::corollary "kerodon_6_3_2_7" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_5_4_6_5, kerodon_6_3_2_5")
Kerodon Corollary 6.3.2.7（[Tag 05ZJ](https://kerodon.net/tag/05ZJ)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Δ³ の二つの指定辺を縮約した Q→Δ⁰ の圏同値。walking equivalence の一点への同値はこの Q を比較しない。

:::

:::corollary "kerodon_6_3_2_8" (uses := "kerodon_6_3_2_7")
Kerodon Corollary 6.3.2.8（[Tag 05ZK](https://kerodon.net/tag/05ZK)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Δ³ の二辺を潰した Q に残る中央の辺 Δ¹→Q が全辺に関する局所化。KST の付着模型とこの Q の比較は未確認。

:::

:::corollary "kerodon_6_3_2_9" (uses := "kerodon_1_1_0_6, kerodon_6_3_2_4, kerodon_6_3_2_8")
Kerodon Corollary 6.3.2.9（[Tag 05ZL](https://kerodon.net/tag/05ZL)）。対応表の状態：なし。

inverseAttachmentはwalkingEquivalenceを貼るpushout。原文の指定Qを貼るpushoutとは別の対象・射であり、Qとの比較なしには同じ局所化の特殊形ではない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.inverseAttachment`、`SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.inverseAttachment_isLocalization`

:::

:::proposition "kerodon_6_3_2_11" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_1_3_2, kerodon_6_3_2_9")
Kerodon Proposition 6.3.2.11（[Tag 05ZP](https://kerodon.net/tag/05ZP)）。対応表の状態：一部。

exists\_quasicategory\_localizationは原文の全ての(C,W)について準圏と局所化射の存在を直接返す。関手性とfiltered colimitの保存は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.edgeLocalization`、`SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.exists_quasicategory_localization`

:::

:::corollary "kerodon_6_3_2_12" (uses := "kerodon_1_1_0_6, kerodon_4_8_8_11, kerodon_6_3_2_11")
Kerodon Corollary 6.3.2.12（[Tag 05ZQ](https://kerodon.net/tag/05ZQ)）。対応表の状態：なし。

引用はcolimitの単体集合c.ptに対する初頂点写像の局所化。原文のarrow categoryのcolimitとなる射との比較、指定辺集合Sが初頂点保存辺集合と一致する比較を型に持たない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap_isLocalization_of_sequential_colimit`

:::

:::proposition "kerodon_6_3_2_13" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_9_5_7, kerodon_6_3_2_9")
Kerodon Proposition 6.3.2.13（[Tag 05ZR](https://kerodon.net/tag/05ZR)）。対応表の状態：なし。

同じ宇宙の局所化の存在は、原文の指定κのessential smallnessが任意の局所化へ移る主張ではない。数値κへの評価と任意標的との比較を欠く。

宣言：`SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.exists_quasicategory_localization`、`SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.edgeLocalization`

:::

# 6.3.3 Reflective Localizations

%%%
number := false
tag := "kerodon-6-3-3"
%%%

Kerodon [Tag 02FY](https://kerodon.net/tag/02FY)

:::definition "kerodon_6_3_3_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization.saturate, SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization, SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertedEdges")
Kerodon Definition 6.3.3.1（[Tag 04JG](https://kerodon.net/tag/04JG)）。対応表の状態：本体にある。

IsLocalization F WをWで存在量化すれば原文の定義そのもの。さらにIsLocalization.saturateでFが反転する全辺をWに選べる。専用のlocalization functorという名前がないことをpartial理由にしない。

:::

:::proposition "kerodon_6_3_3_3" (lean := "SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization.saturate, SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertedEdges")
Kerodon Proposition 6.3.3.3（[Tag 04JH](https://kerodon.net/tag/04JH)）。対応表の状態：本体にある。

仮定：∞ 圏間の F（Lean が弱い：saturate 自体は単体集合間で成立）。結論：ある W について IsLocalization F W なら反転する全辺についても IsLocalization。逆は全辺を W に選ぶ（一致）。

:::

:::definition "kerodon_6_3_3_4"
Kerodon Definition 6.3.3.4（[Tag 02G9](https://kerodon.net/tag/02G9)）。対応表の状態：一部。

Fを選んだReflectiveSubcategoryのreflectorに限ると、構造のadjunctionは同じFの右随伴が充満包含であると直接与える。任意Fを指定して定める述語全体は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ReflectiveSubcategory`、`SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ReflectiveSubcategory.inclusion_fullyFaithful`

:::

:::proposition "kerodon_6_3_3_7"
Kerodon Proposition 6.3.3.7（[Tag 04JL](https://kerodon.net/tag/04JL)）。対応表の状態：一部。

右随伴と可逆counitを指定した場合、QCatAdjunction.isLocalizationは同じFの局所化性を直接与え、右随伴の存在と合わせて原文(2)を返す。右随伴の充満忠実性からのcounit比較・逆方向は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ReflectiveSubcategory.isLocalization`、`SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.isLocalization`

:::

:::definition "kerodon_6_3_3_9"
Kerodon Variant 6.3.3.9（[Tag 04JR](https://kerodon.net/tag/04JR)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：充満忠実な左随伴を持つ右関手としての coreflective localization。AdjointLocalization は可逆余単位をもつ左関手側。

:::

# 6.3.4 Fiberwise Localization

%%%
number := false
tag := "kerodon-6-3-4"
%%%

Kerodon [Tag 02LU](https://kerodon.net/tag/02LU)

:::theorem "kerodon_6_3_4_1" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_5_1_1_1, kerodon_5_1_4_1, kerodon_6_3_4_2, kerodon_6_3_4_4")
Kerodon Theorem 6.3.4.1（[Tag 038U](https://kerodon.net/tag/038U)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：cocartesian fibration の四角でファイバー局所化と底の局所化から全空間の局所化を得る主張。通常の ∞ 圏の局所化はこの輸送条件を持たない。

:::

:::proposition "kerodon_6_3_4_2" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_5_8_1, kerodon_5_1_1_1, kerodon_5_1_4_1, kerodon_5_1_4_17, kerodon_5_1_7_15, kerodon_5_3_6_9")
Kerodon Proposition 6.3.4.2（[Tag 02LW](https://kerodon.net/tag/02LW)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：同じ底上の cocartesian fibration 間でファイバーごとの指定辺を反転した局所化の比較。relativeFunctorPost の同値は各ファイバーが局所化である条件を使わない。

:::

:::corollary "kerodon_6_3_4_3" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_5_1_4_1, kerodon_6_3_1_21, kerodon_6_3_4_2")
Kerodon Corollary 6.3.4.3（[Tag 02LY](https://kerodon.net/tag/02LY)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：弱可縮なファイバーをもつ cocartesian fibration が垂直辺に関する局所化。Kan ファイバーの可縮性から同値を得る型では一般の垂直辺を反転しない。

:::

:::proposition "kerodon_6_3_4_4" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_1_3_3, kerodon_5_1_1_1, kerodon_5_1_1_9, kerodon_5_1_4_1, kerodon_5_3_6_1, kerodon_5_3_6_9, kerodon_5_6_7_2, kerodon_6_3_4_2")
Kerodon Proposition 6.3.4.4（[Tag 038W](https://kerodon.net/tag/038W)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：底の局所化を cocartesian fibration に沿って引き戻し、像が指定の辺となる cocartesian 辺を反転。任意の底変換での cocartesian 性だけでは局所化がない。

:::

:::corollary "kerodon_6_3_4_5"
Kerodon Corollary 6.3.4.5（[Tag 038X](https://kerodon.net/tag/038X)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：底の局所化を left fibration に沿って引き戻したときの局所化。Space 値分類の自然性は反転すべき辺を定めない。

:::

:::proposition "kerodon_6_3_4_6"
Kerodon Proposition 6.3.4.6（[Tag 02LV](https://kerodon.net/tag/02LV)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：積 K×F が K 側で退化する指定辺に関する局所化。precomposition equivalence の積安定性は局所化の対象となる関手の充満部分圏を指定しない。

:::

# 6.3.5 Universal Localizations

%%%
number := false
tag := "kerodon-6-3-5"
%%%

Kerodon [Tag 02LZ](https://kerodon.net/tag/02LZ)

:::definition "kerodon_6_3_5_1" (uses := "kerodon_1_1_0_6")
Kerodon Definition 6.3.5.1（[Tag 02M0](https://kerodon.net/tag/02M0)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：すべての底変換が、退化辺に写る辺に関する局所化となる universally localizing の定義。IsLocalization は単一の射と辺集合についての条件。

:::

:::proposition "kerodon_6_3_5_3" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_3_4_1_13, kerodon_3_4_1_16, kerodon_6_3_1_13")
Kerodon Proposition 6.3.5.3（[Tag 01N7](https://kerodon.net/tag/01N7)）。対応表の状態：なし。

引用は単体圏の初頂点写像を各頂点とする特定のcubeの局所化。原文の任意の二つのcategorical pushoutと指定Wの和集合の比較への型の対応がない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap_isLocalization_of_isPushout`

:::

:::proposition "kerodon_6_3_5_4" (uses := "kerodon_1_1_0_6, kerodon_1_1_4_12, kerodon_1_4_0_1, kerodon_6_3_1_23, kerodon_6_3_2_12, kerodon_6_3_5_1, kerodon_6_3_5_3")
Kerodon Proposition 6.3.5.4（[Tag 02M1](https://kerodon.net/tag/02M1)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：各 Δⁿ 上の局所化と任意の底変換に対する局所化の条件の同値。頂点ごとの通常の pullback 比較は全単体を試す局所判定ではない。

:::

:::corollary "kerodon_6_3_5_5" (uses := "kerodon_1_1_0_6")
Kerodon Corollary 6.3.5.5（[Tag 02M2](https://kerodon.net/tag/02M2)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：universally localizing なら恒等底変換で退化像の辺の局所化になる帰結。IsLocalization の単調性には universally localizing の入力がない。

:::

:::proposition "kerodon_6_3_5_9" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1")
Kerodon Proposition 6.3.5.9（[Tag 04JT](https://kerodon.net/tag/04JT)）。対応表の状態：一部。

sectionを持つfについて、指定した単体ホモトピーとその全成分をfが反転する条件を明示的に加えればisLocalization\_of\_deformationは同じfの局所化を直接返す。universalに要求される底変換のうち恒等底変換の成分だけで、任意底変換ではない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DeformationLocalization.isLocalization_of_deformation`

:::

:::proposition "kerodon_6_3_5_10"
Kerodon Proposition 6.3.5.10（[Tag 02M6](https://kerodon.net/tag/02M6)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：universally localizing なら各次数で全射。dgUniversalCommaTarget\_degree\_surjective は特定の dg 比較写像だけの全射性。

:::

:::proposition "kerodon_6_3_5_11"
Kerodon Proposition 6.3.5.11（[Tag 02M7](https://kerodon.net/tag/02M7)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：任意の二つの universally localizing 射の合成安定性。一般の射のクラスの universally 構成と局所化クラスの合成との同定はない。

:::

:::corollary "kerodon_6_3_5_12"
Kerodon Corollary 6.3.5.12（[Tag 02M8](https://kerodon.net/tag/02M8)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：弱可縮な K を積に足した X×K→S が universally localizing。弱ホモトピー同値な射影の型に任意の底変換の辺の局所化はない。

:::

:::proposition "kerodon_6_3_5_13" (uses := "kerodon_1_1_0_6, kerodon_6_3_2_12, kerodon_6_3_5_4")
Kerodon Proposition 6.3.5.13（[Tag 02M9](https://kerodon.net/tag/02M9)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：arrow 圏で universally localizing 射がフィルター余極限に閉じること。初頂点写像の可算余極限は任意の引き戻しを量化しない。

:::

:::proposition "kerodon_6_3_5_14" (uses := "kerodon_1_1_0_6, kerodon_4_5_5_11, kerodon_6_3_5_3, kerodon_6_3_5_4")
Kerodon Proposition 6.3.5.14（[Tag 02MA](https://kerodon.net/tag/02MA)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：指定 pushout の三射が universally localizing なら残りの射も同様。pushout の anodyne 閉性では退化像の辺の局所化にならない。

:::

# 6.3.6 Subdivision and Localization

%%%
number := false
tag := "kerodon-6-3-6"
%%%

Kerodon [Tag 02MC](https://kerodon.net/tag/02MC)

:::theorem "kerodon_6_3_6_1"
Kerodon Theorem 6.3.6.1（[Tag 02MD](https://kerodon.net/tag/02MD)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：任意の単体集合 S に半順序の nerve から universally localizing 射があること。単体の圏の初頂点射の局所化は定義域が半順序とは限らない。

:::

:::proposition "kerodon_6_3_6_2" (uses := "kerodon_1_1_0_6, kerodon_1_1_4_12, kerodon_3_3_3_1, kerodon_3_3_4_3, kerodon_6_3_5_9, kerodon_6_3_5_13, kerodon_6_3_5_14")
Kerodon Proposition 6.3.6.2（[Tag 02ME](https://kerodon.net/tag/02ME)）。対応表の状態：なし。

sdとsubdivisionLastVertexMapは原文の射の構成まで。局所化・任意の底変換の局所化のいずれもこの型の結論にはない。

宣言：`SSet.sd`、`SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.subdivisionLastVertexMap`

:::

:::definition "kerodon_6_3_6_4"
Kerodon Variant 6.3.6.4（[Tag 04JU](https://kerodon.net/tag/04JU)）。対応表の状態：なし。

transportSimplexFirstVertexMapはN(Δ\_S)からSへの初頂点写像。原文はN(Δ\_S)からSd(S)への指定ψであり、始域が同じだけで別の射。

宣言：`SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.transportSimplexFirstVertexMap_isLocalization`

:::

:::corollary "kerodon_6_3_6_5"
Kerodon Corollary 6.3.6.5（[Tag 04JV](https://kerodon.net/tag/04JV)）。対応表の状態：なし。

引用は初頂点写像の局所化。原文はSdを経由する最終頂点写像の合成で、同じ射に比較する型がない。局所化性とuniversal性の差に先立ち射が異なる。

宣言：`SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.transportSimplexFirstVertexMap_isLocalization`、`SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.transportSimplexFirstVertexMap_ulift_isLocalization`

:::

:::definition "kerodon_6_3_6_6" (lean := "SSet.Nonsingular")
Kerodon Definition 6.3.6.6（[Tag 02MG](https://kerodon.net/tag/02MG)）。対応表の状態：Mathlib にある。

仮定：任意の単体集合 S（Kerodon と一致）。結論：Nonsingular S は各非退化単体の Yoneda に対応する Δⁿ→S が単射であること（一致）。

:::

:::corollary "kerodon_6_3_6_13"
Kerodon Corollary 6.3.6.13（[Tag 02MP](https://kerodon.net/tag/02MP)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：nonsingular S を半順序 nerve から universally localizing に解消。薄い nerve の内ファイブレーションにはこの存在条件がない。

:::

:::proposition "kerodon_6_3_6_14"
Kerodon Proposition 6.3.6.14（[Tag 02MQ](https://kerodon.net/tag/02MQ)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：任意の S に対して nonsingular な始域を持つ universally localizing 射の存在。inner anodyne resolution は通常逆向き。

:::

:::lemma_ "kerodon_6_3_6_15"
Kerodon Lemma 6.3.6.15（[Tag 02MR](https://kerodon.net/tag/02MR)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：nonsingular 単体集合の極限での閉性。presheaf の点ごとの極限は非退化単体の頂点が相異なる性質を特定しない。

:::

:::definition "kerodon_6_3_6_17"
Kerodon Variant 6.3.6.17（[Tag 02MU](https://kerodon.net/tag/02MU)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：有限な S に対し有限半順序の nerve からの universally localizing な表示。一般の単体圏からの局所化は有限性と半順序性を同時に主張しない。

:::

