import Verso
import VersoManual
import VersoBlueprint
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.CocartesianInnerAnodynePullback
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.CocartesianInnerHornPullback
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.LeftFibrationInnerHornPullback
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndLeftKanPreservation
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftCommaUniversalCriterion
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeLeftCanonicalExistence
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.PrecompositionEquivalence
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.InnerAnodyneReplacement
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.Completion
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CompletionBaseChange
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.UniversalProperty

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "8.7 Fiberwise Cocompletions" =>
%%%
number := false
tag := "kerodon-8-7"
%%%

Kerodon の 8.7 節（[Tag 05K8](https://kerodon.net/tag/05K8)）の項目と、SerrePositivity・Mathlib の宣言との対応。本文は対応表（research/kerodon-coverage）の判定の理由の要約で、Kerodon の本文の写しではない。

:::definition "kerodon_8_7_0_1"
Kerodon Definition 8.7.0.1（[Tag 05K9](https://kerodon.net/tag/05K9)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：絶対的な前層の左 Kan 延長と大域的カルテシアン射の反変輸送を確認した。各ファイバーの余完備化・H の充満忠実性・局所カルテシアン性・反変輸送の小余極限保存を束ねる定義は未確認。

:::

:::theorem "kerodon_8_7_0_2"
Kerodon Theorem 8.7.0.2（[Tag 05KA](https://kerodon.net/tag/05KA)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：単独の前層圏の余極限、米田に沿う延長、固定標的の相対指数のカルテシアン性を確認した。任意の本質的小さい内ファイブレーションから必要な全空間を構成し、その底上の一意性を示す型は未確認。

:::

# 8.7.1 Uniqueness of Fiberwise Cocompletions

%%%
number := false
tag := "kerodon-8-7-1"
%%%

Kerodon [Tag 05KB](https://kerodon.net/tag/05KB)

:::definition "kerodon_8_7_1_1"
Kerodon Definition 8.7.1.1（[Tag 05KK](https://kerodon.net/tag/05KK)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：κ-filtered 余完備化の絶対的制限同値と、共変表現可能関手はある。Δ¹ の両ファイバーでの余完備化と、始点から終点への全空間 Hom の K-余極限保存を含む四条件の定義は未確認。

:::

:::proposition "kerodon_8_7_1_4"
Kerodon Proposition 8.7.1.4（[Tag 05KP](https://kerodon.net/tag/05KP)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：大域的カルテシアン射の反変辺輸送と絶対的 Ind の制限同値を確認した。Δ¹ 上で余完備化条件を、カルテシアン性と反変輸送の κ-小余極限保存に置き換える iff は未確認。

:::

:::definition "kerodon_8_7_1_5"
Kerodon Definition 8.7.1.5（[Tag 05KR](https://kerodon.net/tag/05KR)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：底変換と絶対的な κ-filtered 余完備化を確認した。任意の底の全辺に量化し、引戻しがそれぞれファイバーごとの K-余完備化であるという定義は未確認。

:::

:::proposition "kerodon_8_7_1_11"
Kerodon Proposition 8.7.1.11（[Tag 05L0](https://kerodon.net/tag/05L0)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：単独の準圏の冪等完備化と前合成の充満忠実性はある。底上の二つの内ファイブレーションを比較し、各ファイバーの冪等完備化と H の充満忠実性で原文の条件を特徴付ける iff は未確認。

:::

:::proposition "kerodon_8_7_1_12"
Kerodon Proposition 8.7.1.12（[Tag 05KW](https://kerodon.net/tag/05KW)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：絶対的な余完備化の候補と大域的反変輸送を確認した。任意の底で局所カルテシアン性と各輸送の κ-余連続性を用いる、原文の四条件による特徴付けは未確認。

:::

:::definition "kerodon_8_7_1_13"
Kerodon Notation 8.7.1.13（[Tag 05L2](https://kerodon.net/tag/05L2)）。対応表の状態：なし。

全小余極限保存の固定二圏間の全部分圏と辺を保存する相対関手は候補だが、原文の全ファイバーで指定K-余極限を保存する条件を持つ同じ部分圏とは比較していない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrLFunctorSpace`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorSpace`

:::

:::theorem "kerodon_8_7_1_14"
Kerodon Theorem 8.7.1.14（[Tag 05L3](https://kerodon.net/tag/05L3)）。対応表の状態：なし。

局所余錐を追加する相対Kan制限の型は、原文のfiberwise K-cocompletionからその局所条件とK-cocontinuousな部分圏を同定する型を持たない。絶対Indの制限同値は別の射。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeLeftKanRestriction_trivialKanFibration`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indKappaContinuousRestrictionEquivalence`

:::

:::lemma_ "kerodon_8_7_1_17" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indLeftKanExtension_preservesSmallKappaFilteredColimits, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanIsRelativeLeftKanExtendedFrom_iff_universal_fibers")
Kerodon Lemma 8.7.1.17（[Tag 05L7](https://kerodon.net/tag/05L7)）。対応表の状態：一部。

底を終対象、完備化を小準圏のIndκ、Kを小κ-filtered形状に限るとindLeftKanExtension\_preservesSmallKappaFilteredColimitsは同じFについて(2)⇒(1)を直接返す。(3)との同値と任意Kは含まない。

:::

:::lemma_ "kerodon_8_7_1_18"
Kerodon Lemma 8.7.1.18（[Tag 05L8](https://kerodon.net/tag/05L8)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：左 Kan 形状の comma との前合成同値と、右共終性を slice に運ぶ補題はある。原文の E\_\{/X\} の底の恒等射上にある部分の包含が右共終になる型は未確認。

:::

:::proposition "kerodon_8_7_1_19"
Kerodon Proposition 8.7.1.19（[Tag 05L9](https://kerodon.net/tag/05L9)）。対応表の状態：なし。

comma余錐ごとの相対余極限判定は、原文の底の各ファイバーでのK-cocontinuityの判定ではない。原文の指定Hに沿う同じ相対Kan条件への比較を引用に持たない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanIsRelativeLeftKanExtendedFrom_iff_universal_fibers`

:::

:::definition "kerodon_8_7_1_20" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.exists_kanRelativeLeftCanonical_strict_extension_of_local_relative_colimits")
Kerodon Variant 8.7.1.20（[Tag 05LA](https://kerodon.net/tag/05LA)）。対応表の状態：一部。

同じ包含をmonoかつinner fibration、同じU′をequivalence liftingとし全標準comma余錐の相対余極限も追加するとexists\_kanRelativeLeftCanonical\_strict\_extension\_of\_local\_relative\_colimitsが同じ持ち上げ問題の相対左Kan解を直接返す。K-余完備性だけの場合は含まない。

:::

:::lemma_ "kerodon_8_7_1_21"
Kerodon Lemma 8.7.1.21（[Tag 05LB](https://kerodon.net/tag/05LB)）。対応表の状態：なし。

全相対左Kan拡張の制限のtrivial Kan性は、原文のファイバーごとK-cocontinuousな全関手の同じ制限との比較がなく別の部分圏。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeLeftKanRestriction_trivialKanFibration`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeLeftKanRestriction_isFullyFaithful`

:::

# 8.7.2 Fiberwise Cocompletions of Cocartesian Fibrations

%%%
number := false
tag := "kerodon-8-7-2"
%%%

Kerodon [Tag 05LC](https://kerodon.net/tag/05LC)

:::theorem "kerodon_8_7_2_1"
Kerodon Theorem 8.7.2.1（[Tag 05LD](https://kerodon.net/tag/05LD)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：共変輸送、余カルテシアン辺を保つ相対関手、および絶対的 Ind の制限同値はある。余カルテシアン射のファイバーごとの K-余完備化の四条件による特徴付けと存在は未確認。

:::

:::lemma_ "kerodon_8_7_2_2"
Kerodon Lemma 8.7.2.2（[Tag 05LG](https://kerodon.net/tag/05LG)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：指定辺の保存判定と絶対的 Ind の余極限保存はある。原文の各ファイバーと各輸送の条件から、Δ¹ 上の全空間 Hom が K-余極限を保つことを導く向きは未確認。

:::

:::lemma_ "kerodon_8_7_2_3"
Kerodon Lemma 8.7.2.3（[Tag 05LJ](https://kerodon.net/tag/05LJ)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：底上の相対指数へのカリー化と個別の前層の延長はある。余カルテシアン双対を表す K の転置が、指定した相対指数で余完備化条件と余カルテシアン性を満たす結果は未確認。

:::

:::lemma_ "kerodon_8_7_2_5"
Kerodon Lemma 8.7.2.5（[Tag 05LM](https://kerodon.net/tag/05LM)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：一つの準圏の Ind・前層側の構成を確認した。一般の K で、任意の余カルテシアン射の各ファイバーの完備化を底上にまとめる存在は未確認。

:::

# 8.7.3 Fiberwise Cocompletion of Cartesian Fibrations

%%%
number := false
tag := "kerodon-8-7-3"
%%%

Kerodon [Tag 05LR](https://kerodon.net/tag/05LR)

:::theorem "kerodon_8_7_3_1"
Kerodon Theorem 8.7.3.1（[Tag 05LS](https://kerodon.net/tag/05LS)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：反変輸送と逆圏でのカルテシアン辺の判定、絶対的 Ind の制限同値を確認した。各反変輸送の K-余連続性を含む四条件の iff と、そのような全空間の存在は未確認。

:::

:::lemma_ "kerodon_8_7_3_2"
Kerodon Lemma 8.7.3.2（[Tag 05LU](https://kerodon.net/tag/05LU)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：持ち上げ辺の反変輸送と相対左 Kan 延長の局所判定を確認した。カルテシアン性とファイバーの完備化から原文の全空間 Hom の K-余極限保存まで導く片方向は未確認。

:::

:::proposition "kerodon_8_7_3_3"
Kerodon Proposition 8.7.3.3（[Tag 05LV](https://kerodon.net/tag/05LV)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：逆圏での Tw 比較と反変輸送はある。二つの共役の Tw 引戻しの正方形を相対関手同型で可換にする H† と、その H† が K-余完備化になる結果は未確認。

:::

:::corollary "kerodon_8_7_3_4"
Kerodon Corollary 8.7.3.4（[Tag 05LY](https://kerodon.net/tag/05LY)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：カルテシアン射の逆圏での持ち上げと、固定圏の絶対的な余完備化の候補はある。任意の K で、カルテシアン辺を保つ H† が底上の各ファイバーを余完備化する存在は未確認。

:::

# 8.7.4 Existence of Fiberwise Cocompletions

%%%
number := false
tag := "kerodon-8-7-4"
%%%

Kerodon [Tag 05M1](https://kerodon.net/tag/05M1)

:::theorem "kerodon_8_7_4_1"
Kerodon Theorem 8.7.4.1（[Tag 05M2](https://kerodon.net/tag/05M2)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：固定圏の余完備化と底上での相対指数を確認した。任意の内ファイブレーションで、各辺上の K-余完備化をまとめた全空間の存在は未確認。

:::

:::lemma_ "kerodon_8_7_4_2"
Kerodon Lemma 8.7.4.2（[Tag 05M3](https://kerodon.net/tag/05M3)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：前層の Ind 頂点の閉性と、一般の全部分圏の準圏性はある。大きい完備化の各ファイバー内で指定部分圏の最小 K-余極限閉包を取り、底上で制限して再び完備化を得る結果は未確認。

:::

:::lemma_ "kerodon_8_7_4_3"
Kerodon Lemma 8.7.4.3（[Tag 05M6](https://kerodon.net/tag/05M6)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：固定標的への相対指数のカルテシアン性と固定圏の余完備化はある。元が isofibration のとき全空間の K-余完備化を isofibration として選べる結論は未確認。

:::

:::lemma_ "kerodon_8_7_4_4"
Kerodon Lemma 8.7.4.4（[Tag 05M7](https://kerodon.net/tag/05M7)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：底変換の引戻しと、既存の標的への関手の相対左 Kan 延長を確認した。指定した部分底上の完備化自体を固定し、全底で完備化を作って制限の同型を与える結論は未確認。

:::

# 8.7.5 Application: Flat Inner Fibrations

%%%
number := false
tag := "kerodon-8-7-5"
%%%

Kerodon [Tag 05ML](https://kerodon.net/tag/05ML)

:::definition "kerodon_8_7_5_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianFibration_innerHorn_pullback_isPrecompositionEquivalence, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftFibration_innerHorn_pullback_isPrecompositionEquivalence, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianFibration_pullback_innerAnodyne_isPrecompositionEquivalence")
Kerodon Definition 8.7.5.1（[Tag 05MM](https://kerodon.net/tag/05MM)）。対応表の状態：一部。

Uをcocartesian fibrationに限り同じ2単体に沿って引き戻すとcocartesianFibration\_innerHorn\_pullback\_isPrecompositionEquivalenceのn=2,k=1が原文の同じhorn引戻しのcategorical equivalenceを返す。一般inner fibrationのflat条件の判定は含まない。

:::

:::theorem "kerodon_8_7_5_6" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion.pre_isQCatEquivalence, SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion, SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion.pullback_rightFibration")
Kerodon Theorem 8.7.5.6（[Tag 05MS](https://kerodon.net/tag/05MS)）。対応表の状態：一部。

底写像を準圏間のinner fibrationかつ冪等完備化、Uをright fibrationに強めると、pullback\_rightFibrationと前合成普遍性は同じ引戻し射のMorita条件を直接返す。任意flat Uと任意Morita射は含まない。

:::

:::corollary "kerodon_8_7_5_7"
Kerodon Corollary 8.7.5.7（[Tag 05MT](https://kerodon.net/tag/05MT)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：内アノダインでの頂点全単射と余カルテシアン底変換での前合成同値はある。一般の内ファイブレーションの底変換で、Morita、圏同値、頂点全射の圏同値の三条件が対応する結果は未確認。

:::

:::corollary "kerodon_8_7_5_8"
Kerodon Corollary 8.7.5.8（[Tag 05MU](https://kerodon.net/tag/05MU)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：前合成同値の合成と、余カルテシアン射に沿う内ホーンの比較はある。二つの flat 内ファイブレーションの合成が再び flat となる閉性は確認できない。

:::

:::proposition "kerodon_8_7_5_9"
Kerodon Proposition 8.7.5.9（[Tag 05MV](https://kerodon.net/tag/05MV)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：カルテシアン射の辺輸送と絶対的な Ind、余カルテシアン射のホーン比較はある。本質的 κ-小な U の flat 性と κ-余完備化した射のカルテシアン性を比較する iff は未確認。

:::

:::lemma_ "kerodon_8_7_5_11"
Kerodon Lemma 8.7.5.11（[Tag 05MX](https://kerodon.net/tag/05MX)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：固定した始域からの二関手の全自然な retract では κ-filtered 余極限保存を移せる。原文は底 hC の頂点間の retract から、異なるファイバーへの制限が指定 K-余極限を保つことを移す。この比較は未確認。

:::

:::lemma_ "kerodon_8_7_5_12"
Kerodon Lemma 8.7.5.12（[Tag 05MY](https://kerodon.net/tag/05MY)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：冪等完備化の絶対的な制限と内アノダイン底変換を確認した。完備化側がカルテシアンという仮定から元の E で任意の Morita 射の底変換を示す結果は未確認。

:::

:::lemma_ "kerodon_8_7_5_13"
Kerodon Lemma 8.7.5.13（[Tag 05MZ](https://kerodon.net/tag/05MZ)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：内ホーン引戻しの同値には既存の余カルテシアン性が必要。原文は Δ² 上のホーン引戻しの同値でファイバーごとの完備化後のカルテシアン性を判定する。この iff は未確認。

:::

:::corollary "kerodon_8_7_5_14" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianFibration_innerHorn_pullback_isPrecompositionEquivalence, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianFibration_pullback_innerAnodyne_isPrecompositionEquivalence")
Kerodon Corollary 8.7.5.14（[Tag 05N0](https://kerodon.net/tag/05N0)）。対応表の状態：一部。

Uにcocartesian fibrationを追加すると、各2単体でのinner hornの引戻し同値から原文の同じUのflat条件を直接得る。任意のΔ1への関手の場合は含まない。

:::

:::corollary "kerodon_8_7_5_16"
Kerodon Corollary 8.7.5.16（[Tag 05N2](https://kerodon.net/tag/05N2)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：任意の引戻しの構成と余カルテシアン射での内ホーン引戻しを確認した。Δ² 上で非退化な 2 単体だけを調べれば flat の全条件が従う iff は未確認。

:::

:::proposition "kerodon_8_7_5_17"
Kerodon Proposition 8.7.5.17（[Tag 05N3](https://kerodon.net/tag/05N3)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：厳密な単体集合の slice での底変換の右随伴と、ファイバーごとの相対指数を確認した。準圏の圏における指数可能性を flat isofibration と同値にする型は未確認。

:::

:::corollary "kerodon_8_7_5_19"
Kerodon Corollary 8.7.5.19（[Tag 05N5](https://kerodon.net/tag/05N5)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：厳密な単体集合の slice の随伴と特定のファイブレーションのホーン比較はある。全 Δⁿ 上の準圏論的指数可能性との同値および n=2 による判定は未確認。

:::

:::lemma_ "kerodon_8_7_5_20"
Kerodon Lemma 8.7.5.20（[Tag 05N6](https://kerodon.net/tag/05N6)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：左ファイブレーション間で全体の同値をファイバーに移す比較と、冪等完備化の制限を調べた。flat 内ファイブレーションを全空間の同値で移し、各ファイバーが Morita 同値になる結論は未確認。

:::

:::proposition "kerodon_8_7_5_22" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.exists_innerAnodyne_innerFibration_factorization, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isPrecompositionEquivalence_of_innerAnodyne")
Kerodon Proposition 8.7.5.22（[Tag 05N8](https://kerodon.net/tag/05N8)）。対応表の状態：一部。

同じUのinner anodyne/inner fibration分解とinner anodyneのcategorical equivalence性から、中間準圏への同値Fとinner fibration U′という結論成分を直接得る。U′のflat/isofibration性と各ファイバーのMorita条件は含まない。

:::

:::corollary "kerodon_8_7_5_23"
Kerodon Corollary 8.7.5.23（[Tag 05N9](https://kerodon.net/tag/05N9)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：冪等完備性、同値持ち上げ、大域的カルテシアン輸送は個別にある。flat 性と冪等完備なファイバーから同値持ち上げを回収し指数可能にする結論は未確認。

:::

:::proposition "kerodon_8_7_5_24"
Kerodon Proposition 8.7.5.24（[Tag 05NA](https://kerodon.net/tag/05NA)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：内アノダインの前合成同値、既存の射の底変換、左ファイブレーションの部分複体上の比較はある。頂点を全て含む圏同値に沿い、指定の flat 射が厳密に引戻しとなる延長の存在は未確認。

:::

:::corollary "kerodon_8_7_5_26"
Kerodon Corollary 8.7.5.26（[Tag 05NC](https://kerodon.net/tag/05NC)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：底を準圏にする内アノダイン分解と既存の射の引戻しは確認した。その底拡大に沿って flat 内ファイブレーションを延長し、元の射を引戻しで回収する型は未確認。

:::

:::corollary "kerodon_8_7_5_27"
Kerodon Corollary 8.7.5.27（[Tag 05ND](https://kerodon.net/tag/05ND)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：同値持ち上げの述語と冪等完備性、およびカルテシアン辺を逆圏で扱う補題はある。任意の底上で flat 性とファイバーの冪等完備性から isofibration を得る結論は未確認。

:::

:::corollary "kerodon_8_7_5_28"
Kerodon Corollary 8.7.5.28（[Tag 05NE](https://kerodon.net/tag/05NE)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：一つの準圏を冪等完備化する型と同値持ち上げの述語はある。元の flat 射のファイバーごとの冪等完備化が同時に flat かつ isofibration になる定理は未確認。

:::

:::proposition "kerodon_8_7_5_29"
Kerodon Proposition 8.7.5.29（[Tag 05NF](https://kerodon.net/tag/05NF)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：底の内アノダイン準圏置換と引戻しは個別にある。拡大した底で同値持ち上げと flat 性を両方保つ延長の存在は確認できない。

:::

:::corollary "kerodon_8_7_5_30"
Kerodon Corollary 8.7.5.30（[Tag 05NG](https://kerodon.net/tag/05NG)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：厳密な単体集合の slice の右随伴と、余カルテシアンな定義域を持つ相対指数のカルテシアン性を確認した。flat isofibration が準圏の圏で指数可能になる型は未確認。

:::

# 8.7.6 Flatness and Morphism Spaces

%%%
number := false
tag := "kerodon-8-7-6"
%%%

Kerodon [Tag 05NH](https://kerodon.net/tag/05NH)

:::theorem "kerodon_8_7_6_1"
Kerodon Theorem 8.7.6.1（[Tag 05NJ](https://kerodon.net/tag/05NJ)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：合成可能な二辺を固定した三角形充填の空間は Kan 可縮。原文は長辺 f と底の中間頂点を固定して中間対象を動かす二重 slice の弱可縮性を、flat 性と同値にする。この比較は未確認。

:::

:::lemma_ "kerodon_8_7_6_2"
Kerodon Lemma 8.7.6.2（[Tag 05NK](https://kerodon.net/tag/05NK)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：余表現関手と左 Kan 拡張の comma 模型を確認した。flat 性を使い、終点側二頂点上の余表現関手が中央ファイバーから左 Kan 拡張される結論は未確認。

:::

:::lemma_ "kerodon_8_7_6_3"
Kerodon Lemma 8.7.6.3（[Tag 05NL](https://kerodon.net/tag/05NL)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：余米田の充満忠実性と左 Kan 判定、固定二辺の充填可縮性はある。始点ファイバーの各 X の余表現関手が中央から左 Kan 拡張されれば U が flat になる向きは未確認。

:::

:::proposition "kerodon_8_7_6_4"
Kerodon Proposition 8.7.6.4（[Tag 05NM](https://kerodon.net/tag/05NM)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：左共終性の判定と別の coslice 射の右共終性を確認した。始点対象 X の coslice で、中央ファイバーから後半辺の引戻しへの包含が左共終となることと flat 性の同値は未確認。

:::

# 8.7.7 Fiberwise Cocompletion via the Yoneda Embedding

%%%
number := false
tag := "kerodon-8-7-7"
%%%

Kerodon [Tag 05NN](https://kerodon.net/tag/05NN)

:::proposition "kerodon_8_7_7_1"
Kerodon Proposition 8.7.7.1（[Tag 05NP](https://kerodon.net/tag/05NP)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：固定標的相対指数の既存の射影は余カルテシアンな定義域のもとでカルテシアン。原文の flat な定義域における余カルテシアン性、およびその共役が逆圏側の余完備化となる結論は未確認。

:::

:::lemma_ "kerodon_8_7_7_2"
Kerodon Lemma 8.7.7.2（[Tag 05NQ](https://kerodon.net/tag/05NQ)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：相対指数の各ファイバーの同定と、余カルテシアン射に付随する輸送の一般論はある。原文の指数の余カルテシアン射影と、その輸送の κ-小余極限保存は未確認。

:::

:::definition "kerodon_8_7_7_3"
Kerodon Construction 8.7.7.3（[Tag 05NR](https://kerodon.net/tag/05NR)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：固定形状のマーク付き相対関手とその切断の評価はある。変動する Tw ファイバーの指定辺を保つ切断を全底でまとめ、その評価を共役とする構成は未確認。

:::

:::theorem "kerodon_8_7_7_4"
Kerodon Theorem 8.7.7.4（[Tag 05NS](https://kerodon.net/tag/05NS)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：相対 Tw と相対指数のカリー化、および固定圏の米田延長はある。相対 Hom の転置が共役の部分圏を経由し、さらに Eᵒᵖ のファイバーごとの余完備化になる二結論は未確認。

:::

:::lemma_ "kerodon_8_7_7_6"
Kerodon Lemma 8.7.7.6（[Tag 05NU](https://kerodon.net/tag/05NU)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：底変換付きのカリー化と指定辺の保存述語はある。転置が、全ての Tw 始点ファイバーで余カルテシアン辺を保つという共役の部分圏に入る補題は未確認。

:::

:::lemma_ "kerodon_8_7_7_7"
Kerodon Lemma 8.7.7.7（[Tag 05NV](https://kerodon.net/tag/05NV)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：絶対的な余完備化の延長と相対指数はある。相対 Hom の特定の転置から、逆圏の底上で κ-余完備化の条件を得る型は未確認。

:::

:::lemma_ "kerodon_8_7_7_8"
Kerodon Lemma 8.7.7.8（[Tag 05NX](https://kerodon.net/tag/05NX)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：単独の小準圏の余米田の充満忠実性はある。相対 Tw の既存比較は元の射の充満忠実性を仮定する。flat 性から共役の部分圏への相対米田が全空間で充満忠実になる結果は未確認。

:::

