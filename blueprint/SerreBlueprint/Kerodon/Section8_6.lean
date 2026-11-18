import Verso
import VersoManual
import VersoBlueprint
import Mathlib.CategoryTheory.Bicategory.Grothendieck
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.FiberwiseHomPostcomposition
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.Nerve
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCatSimplicial
import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.WeakHomotopy
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FiberwiseHom
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.TrivialFibrationEquivalence
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.CosliceTwistedArrowTarget
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.CosliceTwistedArrowTargetNaturality
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.ConjugateAndDualFibrations.EdgewiseEnrichedCategory
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.EdgewiseEnrichedComparison
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseRightFilling
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseSubdivision
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.HomSwap
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.Projection
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedArrowFunctorComparison

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "8.6 Conjugate and Dual Fibrations" =>
%%%
number := false
tag := "kerodon-8-6"
%%%

Kerodon の 8.6 節（[Tag 04C0](https://kerodon.net/tag/04C0)）の項目と、SerrePositivity・Mathlib の宣言との対応。本文は対応表（research/kerodon-coverage）の判定の理由の要約で、Kerodon の本文の写しではない。

# 8.6.1 Conjugate Fibrations

%%%
number := false
tag := "kerodon-8-6-1"
%%%

Kerodon [Tag 04C6](https://kerodon.net/tag/04C6)

:::definition "kerodon_8_6_1_1" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_5_1_1_1, kerodon_5_1_4_1, kerodon_8_1_1_6")
Kerodon Definition 8.6.1.1（[Tag 04C7](https://kerodon.net/tag/04C7)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：逆圏の辺・持ち上げと Tw の二射影を確認した。原文は全空間を反転せず、Tw(C) 上の T が恒等射のファイバーで同値かつカルテシアン辺を余カルテシアン辺に送るという三条件を課す。この述語に達する宣言は未確認。

:::

:::proposition "kerodon_8_6_1_5"
Kerodon Proposition 8.6.1.5（[Tag 04CB](https://kerodon.net/tag/04CB)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：既存の一意性は同じ余カルテシアン・ファイブレーション上の二つの輸送関手を比較する。原文にある別々のファイブレーションの T\_C を縦辺とする輸送正方形の同型は未確認。

:::

:::corollary "kerodon_8_6_1_6"
Kerodon Corollary 8.6.1.6（[Tag 04CC](https://kerodon.net/tag/04CC)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：既存の輸送の一意性は同一射上で選んだ輸送表示を比較する。原文では共役 T の各 T\_C を成分として異なる二つの表示の自然同型を作る。この成分を持つ比較は未確認。

:::

:::corollary "kerodon_8_6_1_7"
Kerodon Corollary 8.6.1.7（[Tag 04CD](https://kerodon.net/tag/04CD)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：輸送表示の一意性と右ファイブレーションを逆圏で左に移す圏同値を確認した。一般の共役なカルテシアン・余カルテシアン対について hC 上の輸送表示が同型になる結論は未確認。

:::

:::proposition "kerodon_8_6_1_8"
Kerodon Proposition 8.6.1.8（[Tag 04CE](https://kerodon.net/tag/04CE)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Tw(E) の積への左ファイブレーション性、射影の自然性、左ファイブレーションの逆圏を確認した。Tw(E) から Eᵒᵖ×\_\{Cᵒᵖ\}Tw(C) への特定の比較の自明 Kan 性と、その切断による共役は未確認。

:::

:::definition "kerodon_8_6_1_9" (lean := "CategoryTheory.Pseudofunctor.Grothendieck.Hom, CategoryTheory.Pseudofunctor.CoGrothendieck.Hom, CategoryTheory.Pseudofunctor.CoGrothendieck.forget")
Kerodon Construction 8.6.1.9（[Tag 04CF](https://kerodon.net/tag/04CF)）。対応表の状態：一部。

*主張*　通常の圏 $`C` から圏の双圏への関手 $`\mathscr F` の反変な元の圏をねじれ矢印圏と $`C^{\mathrm{op}}` 上で引き戻し、共変な元の圏への関手 $`T` を定める。対象 $`(s:c'\to c,x)` は $`(c,\mathscr F(s)x)` に、$`t=fsf'` と $`u:x\to\mathscr F(f')y` をもつ射は、$`\mathscr F(f)\mathscr F(s)(u)` と合成制約で作る射に移る。

Grothendieck/CoGrothendieckの構成は同じ通常圏値Fのint±という二つの入力圏の対象・射を直接与える。原文のそれらを合わせるTの全構成は含まない。

:::

:::proposition "kerodon_8_6_1_10"
Kerodon Proposition 8.6.1.10（[Tag 04CG](https://kerodon.net/tag/04CG)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：両 Grothendieck 構成の忘却関手と、別模型である重み付き神経の余カルテシアン性はある。原文の T の神経がファイバー同値と辺保存を満たす結論は未確認。

:::

:::definition "kerodon_8_6_1_11" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve")
Kerodon Construction 8.6.1.11（[Tag 04CH](https://kerodon.net/tag/04CH)）。対応表の状態：一部。

*主張*　通常の圏 $`C` 上の無限圏値関手 $`\mathscr F` で、値ごとの反対圏の重み付き神経の反対を $`E^\dagger`、元の重み付き神経を $`E` とする。$`E^\dagger` と $`\operatorname{Tw}(N(C))` の $`N(C)^{\mathrm{op}}` 上の引き戻しから $`E` への写像は、始点側の単体の各始区間を中央の射 $`c'_0\to c_0` と $`c_0\to c_i` に沿って移して重みの列を作る。

weightedNerveとその射影は同じ通常圏値FのE側の加重脈体と底への射影を直接与える。反対側を併せたTという全構成は含まない。

:::

:::proposition "kerodon_8_6_1_12"
Kerodon Proposition 8.6.1.12（[Tag 04CJ](https://kerodon.net/tag/04CJ)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：重み付き神経の射影の余カルテシアン性と辺を逆圏に送る比較はある。原文の点ごとに逆圏を取った重みを使う T が共役を与える結論は確認できない。

:::

:::proposition "kerodon_8_6_1_13" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_5_1_1_1, kerodon_5_1_4_1, kerodon_5_1_4_12, kerodon_5_1_4_13, kerodon_8_6_1_1")
Kerodon Proposition 8.6.1.13（[Tag 04CK](https://kerodon.net/tag/04CK)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：余カルテシアン辺の三角形での合成・消去を確認した。任意の T の辺保存と、Tw(C) の e\_L に対する余カルテシアン性および e\_R に対するファイバー内同型性との同値は未確認。

:::

# 8.6.2 Existence of Conjugate Fibrations

%%%
number := false
tag := "kerodon-8-6-2"
%%%

Kerodon [Tag 04CM](https://kerodon.net/tag/04CM)

:::definition "kerodon_8_6_2_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomEquiv, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.fiberwiseHomPostcompOver") (uses := "kerodon_1_1_0_6, kerodon_4_5_8_1")
Kerodon Notation 8.6.2.1（[Tag 04CN](https://kerodon.net/tag/04CN)）。対応表の状態：一部。

*主張*　単体集合 $`D\to D_-^{\mathrm{op}}\times D_+` と $`U:E\to D_+` に対し、相対指数対象 $`\operatorname{Fun}(D/D_-^{\mathrm{op}},E)` のうち、$`\Delta^n\times_{D_-^{\mathrm{op}}}D\to E` が $`D_+` 上の射である単体からなる部分集合を $`\operatorname{Fun}_{/D_+}(D/D_-^{\mathrm{op}},E)` と書く。

fiberwiseHomとfiberwiseHomEquivはλ−とEの同じ相対指数対象およびその写像の普遍性を直接与える。追加のD+上の条件で切る部分全体は含まない。

:::

:::definition "kerodon_8_6_2_2" (uses := "kerodon_1_1_0_6, kerodon_5_1_1_1, kerodon_5_1_4_1, kerodon_8_6_2_1")
Kerodon Construction 8.6.2.2（[Tag 04CP](https://kerodon.net/tag/04CP)）。対応表の状態：なし。

markedCocartesianFunctorSpaceは固定始域の関手空間。原文の底の頂点ごとに始域が変わる全相対指数対象の同じ部分圏との比較を引用に持たない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorSpace`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianSectionsEvaluate`

:::

:::proposition "kerodon_8_6_2_3" (uses := "kerodon_1_4_0_1, kerodon_5_1_4_1, kerodon_8_6_2_2, kerodon_8_6_2_7, kerodon_8_6_2_8")
Kerodon Proposition 8.6.2.3（[Tag 04CQ](https://kerodon.net/tag/04CQ)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：固定標的へのファイバーごとの Hom はカルテシアン、固定形状の切断の始点評価には圏同値がある。Tw 上で指定した全部分圏の射影とその評価が同時に共役を与える結論は未確認。

:::

:::corollary "kerodon_8_6_2_4" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_5_1_4_1, kerodon_5_6_7_3, kerodon_8_6_2_3")
Kerodon Corollary 8.6.2.4（[Tag 04CR](https://kerodon.net/tag/04CR)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：逆圏を取ると全空間の各ファイバーも反転する。固定標的を持つファイバーごとの Hom がカルテシアンになる宣言も調べたが、任意の U のファイバーと同値になる共役を構成する結果は未確認。

:::

:::lemma_ "kerodon_8_6_2_6" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_5_8_18, kerodon_5_1_1_1, kerodon_5_1_1_9, kerodon_5_1_4_1, kerodon_5_3_6_1, kerodon_5_3_6_12, kerodon_7_3_5_9, kerodon_8_2_1_7")
Kerodon Lemma 8.6.2.6（[Tag 04CT](https://kerodon.net/tag/04CT)）。対応表の状態：なし。

固定標的のfiberwiseHomProjectionのcartesian性は原文のD+上で制約した相対指数対象の射影ではない。D+を点に限る場合も同じ制約付き対象への比較同型を引用で確認できていない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.fiberwiseHomProjection_cartesianFibration`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.fiberwiseHom_isCartesianEdge_of_inverting`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinRelativeProjection_pre_cartesianFibration`

:::

:::lemma_ "kerodon_8_6_2_7" (uses := "kerodon_1_4_0_1, kerodon_5_1_1_1, kerodon_5_1_2_5, kerodon_5_1_4_1, kerodon_5_1_4_17, kerodon_8_6_2_2, kerodon_8_6_2_6")
Kerodon Lemma 8.6.2.7（[Tag 04CU](https://kerodon.net/tag/04CU)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：指定辺を送る全部分圏の準圏性と、別模型であるファイバーごとの Hom の辺に関する結果はある。原文の Tw の切断をカルテシアン辺で移した際の閉性、射影の制限、辺の反映は確認できない。

:::

:::proposition "kerodon_8_6_2_8" (uses := "kerodon_1_4_0_1, kerodon_5_1_1_1, kerodon_5_1_1_9, kerodon_5_1_4_1, kerodon_5_1_6_1, kerodon_5_3_1_21, kerodon_8_1_2_1, kerodon_8_6_1_1, kerodon_8_6_1_13, kerodon_8_6_2_2, kerodon_8_6_2_6, kerodon_8_6_2_7")
Kerodon Proposition 8.6.2.8（[Tag 04CV](https://kerodon.net/tag/04CV)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：引戻しを用いるカリー化と、固定形状で指定辺を送る条件を確認した。原文の共役条件と Cᵒᵖ 上の変動するマーク付き相対指数への圏同値の同値は未確認。

:::

:::corollary "kerodon_8_6_2_9"
Kerodon Corollary 8.6.2.9（[Tag 05JG](https://kerodon.net/tag/05JG)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：固定した図式へのマーク付き相対関手と、edgewise subdivision を使う別の相対関手の逆圏比較を確認した。共役 T との合成の充満忠実性、および各 Tw ファイバーで辺保存を課す本質像は未確認。

:::

# 8.6.3 Uniqueness of Conjugate Fibrations

%%%
number := false
tag := "kerodon-8-6-3"
%%%

Kerodon [Tag 04EC](https://kerodon.net/tag/04EC)

:::definition "kerodon_8_6_3_1" (uses := "kerodon_1_1_0_6, kerodon_5_1_1_1, kerodon_5_1_4_1, kerodon_8_1_6_1, kerodon_8_1_7_14")
Kerodon Notation 8.6.3.1（[Tag 04ED](https://kerodon.net/tag/04ED)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：既存の edgewise subdivision とマーク付き相対関手は別の構成。右脚が余カルテシアンな Cospan(E) を Cᵒᵖ に引き戻す対象を確認できなかった。

:::

:::proposition "kerodon_8_6_3_5" (uses := "kerodon_1_1_0_6, kerodon_5_1_4_1, kerodon_8_6_2_4, kerodon_8_6_3_9, kerodon_8_6_3_11")
Kerodon Proposition 8.6.3.5（[Tag 05JK](https://kerodon.net/tag/05JK)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：逆圏の持ち上げとファイバーごとの Hom のカルテシアン性を確認した。原文の脚に条件を課した Cospan 引戻しのカルテシアン性と共役性は未確認。

:::

:::lemma_ "kerodon_8_6_3_6" (uses := "kerodon_1_4_0_1, kerodon_5_1_1_1, kerodon_5_1_4_1, kerodon_8_1_6_5, kerodon_8_1_10_9")
Kerodon Lemma 8.6.3.6（[Tag 04EL](https://kerodon.net/tag/04EL)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Mathlib の普通の span の双圏と、単体的集合の逆圏での辺の比較を調べた。Cospan(U) の制限がカルテシアンで、辺が左脚同型かつ右脚余カルテシアンと同値になる主張は未確認。

:::

:::lemma_ "kerodon_8_6_3_8" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_5_1_4_1, kerodon_5_1_4_8, kerodon_8_6_3_6")
Kerodon Lemma 8.6.3.8（[Tag 04EN](https://kerodon.net/tag/04EN)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：既存の辺判定はファイバーごとの Hom のホーン持ち上げ、または逆圏の辺の比較。引き戻した Cospan の辺の二脚と、その一方がファイバー内で同型という判定は未確認。

:::

:::definition "kerodon_8_6_3_9" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowOppositeSwap_projection, SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection_naturality, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.twistedArrowOppositeSwap_left, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.twistedArrowOppositeSwap_right, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.twistedArrowOppositeSwap_naturality") (uses := "kerodon_1_1_0_6, kerodon_8_1_1_6, kerodon_8_1_1_7, kerodon_8_1_3_7")
Kerodon Construction 8.6.3.9（[Tag 04EX](https://kerodon.net/tag/04EX)）。対応表の状態：一部。

*主張*　$`E\to C`、$`E^\dagger\to C^{\mathrm{op}}` と、終域射影と両立する $`T:E^\dagger\times_{C^{\mathrm{op}}}\operatorname{Tw}(C)\to E` を取る。$`\operatorname{Tw}(E^\dagger)` の終域射影を $`T` と合成し、ねじれ矢印と余スパンの随伴で転置すると、$`E^\dagger\to\operatorname{Cospan}(E)\times_{\operatorname{Cospan}(C)}C^{\mathrm{op}}` という比較写像が得られる。

twistedArrowOppositeSwapとその二射影との可換性から、原文の8.87の最初のTw(E†)からの射と底との可換図式を直接構成できる。全相対指数への転置Ψとその比較までは含まない。

:::

:::proposition "kerodon_8_6_3_11" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_5_1_1_1, kerodon_5_1_4_1, kerodon_5_1_7_15, kerodon_8_1_7_6, kerodon_8_6_1_1, kerodon_8_6_1_13, kerodon_8_6_3_1, kerodon_8_6_3_8, kerodon_8_6_3_9")
Kerodon Proposition 8.6.3.11（[Tag 04F2](https://kerodon.net/tag/04F2)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Tw の逆圏比較と別の相対指数のカルテシアン性はある。Ψ がマーク付き Cospan を経由しカルテシアン・ファイブレーションの同値を与えることとの必要十分条件は未確認。

:::

:::corollary "kerodon_8_6_3_14" (uses := "kerodon_1_1_0_6, kerodon_5_1_4_1, kerodon_8_6_3_5, kerodon_8_6_3_11")
Kerodon Corollary 8.6.3.14（[Tag 04F4](https://kerodon.net/tag/04F4)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：輸送表示の一意性は表示の選択を変える結果で、逆圏の同値は右・左ファイブレーション用。任意の余カルテシアン・ファイブレーションに対する共役の存在と、底上のファイブレーションとしての一意性は確認できない。

:::

:::definition "kerodon_8_6_3_15" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionMap")
Kerodon Construction 8.6.3.15（[Tag 05JL](https://kerodon.net/tag/05JL)）。対応表の状態：一部。

*主張*　単体集合 $`C` について、$`\Delta^1` の非退化辺を固定し、ねじれ矢印関手で $`\Delta^1\times\operatorname{Fun}(\Delta^1,C)\to C` の評価を取る。この写像を余スパン関手との随伴で転置して、$`\operatorname{Fun}(\Delta^1,C)\to\operatorname{Cospan}(\operatorname{Tw}(C))` を得る。

edgewiseSubdivisionMapを評価射evに適用したTw(ev)は原文の指定合成の最後の射そのもの。先行するΞと、そのΞを含む合成全体の同値は含まない。

:::

:::proposition "kerodon_8_6_3_17"
Kerodon Proposition 8.6.3.17（[Tag 05JP](https://kerodon.net/tag/05JP)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：edgewise の圏同値は別の enriched nerve 比較。原文の Ξ の標的は Tw(C) から作った脚条件付き Cospan であり、その特定の比較の圏同値は未確認。

:::

:::corollary "kerodon_8_6_3_18"
Kerodon Corollary 8.6.3.18（[Tag 05JQ](https://kerodon.net/tag/05JQ)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：両端評価の内ファイブレーション性、Tw(C) の積への射影および固定始点からの左ファイブレーション性を確認した。原文の始点評価を共役として特徴付ける比較は未確認。

:::

# 8.6.4 Dual Fibrations

%%%
number := false
tag := "kerodon-8-6-4"
%%%

Kerodon [Tag 04D0](https://kerodon.net/tag/04D0)

:::definition "kerodon_8_6_4_1"
Kerodon Definition 8.6.4.1（[Tag 04D1](https://kerodon.net/tag/04D1)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Tw の左ファイブレーション、余カルテシアン辺の合成と輸送を確認した。原文は任意の二つの射の引戻し上の左ファイブレーションに、各ファイバーの balanced coupling と普遍頂点の輸送保存を課す。この述語は未確認。

:::

:::proposition "kerodon_8_6_4_7"
Kerodon Proposition 8.6.4.7（[Tag 04D7](https://kerodon.net/tag/04D7)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：同一射上の輸送関手の一意性と余米田の充満忠実性はある。Δ¹ 上の二つの輸送を両端の coupling の表示関手で結ぶ可換同型正方形は未確認。

:::

:::corollary "kerodon_8_6_4_8"
Kerodon Corollary 8.6.4.8（[Tag 04DA](https://kerodon.net/tag/04DA)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：輸送表示の辺成分・一意性と余米田の頂点評価を確認した。各 coupling の表示 G\_C の同型類を成分とする二つの輸送の自然変換は未確認。

:::

:::corollary "kerodon_8_6_4_9"
Kerodon Corollary 8.6.4.9（[Tag 04DB](https://kerodon.net/tag/04DB)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：同一の余カルテシアン射の輸送表示の一意性と、左・右ファイブレーションの逆圏同値はある。balanced coupling の表示を成分とする、別々の二つの輸送の自然同型は未確認。

:::

:::corollary "kerodon_8_6_4_10"
Kerodon Corollary 8.6.4.10（[Tag 04DC](https://kerodon.net/tag/04DC)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：既存の輸送の対象計算は一つの射を扱い、逆圏同値は底も逆にする。原文の同じ底で各ファイバーだけを逆にした輸送表示と双対側の同型は未確認。

:::

:::definition "kerodon_8_6_4_12" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_5_1_1_1, kerodon_5_1_4_1, kerodon_8_3_2_7, kerodon_8_3_2_18")
Kerodon Definition 8.6.4.12（[Tag 04DE](https://kerodon.net/tag/04DE)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Hom の空間値双関手と単独の余表現可能性を確認した。二つのファイブレーションの同じ底上の辺に対し、全てのファイバーでの balanced 性と普遍頂点の保存を同時に述べる定義は未確認。

:::

:::definition "kerodon_8_6_4_13" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_5_1_4_1, kerodon_8_6_4_12")
Kerodon Variant 8.6.4.13（[Tag 04DF](https://kerodon.net/tag/04DF)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：小さい空間値の余表現可能性と空間の宇宙変更はある。任意の非可算 κ で局所 κ-小なファイバーを許し、S\_\{\<κ\} に値を取る相対 balanced pairing の条件は未確認。

:::

:::proposition "kerodon_8_6_4_15"
Kerodon Proposition 8.6.4.15（[Tag 04DH](https://kerodon.net/tag/04DH)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：左ファイブレーションの底変換、Tw の左ファイブレーション性、単一関手の余表現可能性を確認した。原文の左ファイブレーションの双対データと S\_\{\<κ\} 値 pairing の存在の同値は未確認。

:::

:::proposition "kerodon_8_6_4_16"
Kerodon Proposition 8.6.4.16（[Tag 04DJ](https://kerodon.net/tag/04DJ)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：全空間の端点対は内ファイブレーションで、左ファイブレーションは引戻しで保存される。底で恒等な矢印だけを取った相対経路の E×\_C E への射影の左ファイブレーション性と自己双対性は未確認。

:::

:::corollary "kerodon_8_6_4_17"
Kerodon Corollary 8.6.4.17（[Tag 04DK](https://kerodon.net/tag/04DK)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Kan 複体の両端評価のファイブレーション性と左ファイブレーションの逆圏を確認した。原文の同じ底・同じ全空間に対する自己双対性は未確認。

:::

:::proposition "kerodon_8_6_4_19"
Kerodon Proposition 8.6.4.19（[Tag 04DM](https://kerodon.net/tag/04DM)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：擬関手の Grothendieck 射影と重み付き神経の余カルテシアン射影はある。F と点ごとの Fᵒᵖ の二つの Grothendieck 射影の神経を双対として比較する宣言は未確認。

:::

:::definition "kerodon_8_6_4_20"
Kerodon Construction 8.6.4.20（[Tag 04DN](https://kerodon.net/tag/04DN)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Grothendieck 構成の射と通常の二変数関手のカリー化を調べた。二つの Grothendieck 全空間を底上で引き戻し、射に対して F(u) と二つのファイバー射を合成する Set 値 K は未確認。

:::

:::proposition "kerodon_8_6_4_21"
Kerodon Proposition 8.6.4.21（[Tag 04DP](https://kerodon.net/tag/04DP)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の忘却関手、集合の神経の空間への埋め込みを確認した。指定のファイバー Hom 関手の神経が二つの射影の余カルテシアン双対を与える型は未確認。

:::

:::proposition "kerodon_8_6_4_22"
Kerodon Proposition 8.6.4.22（[Tag 04DQ](https://kerodon.net/tag/04DQ)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：重み付き神経の射影は余カルテシアンで、係数変換は余カルテシアン辺を保存する。点ごとの逆圏を重みとした射影との双対性は未確認。

:::

:::proposition "kerodon_8_6_4_23"
Kerodon Proposition 8.6.4.23（[Tag 04DR](https://kerodon.net/tag/04DR)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：重みの自然変換から底上の射を作る宣言と、Tw の積への射影の自然性を確認した。原文の二つの重み付き神経の引戻しを標的にした pairing の双対性は未確認。

:::

# 8.6.5 Existence of Dual Fibrations

%%%
number := false
tag := "kerodon-8-6-5"
%%%

Kerodon [Tag 04DS](https://kerodon.net/tag/04DS)

:::theorem "kerodon_8_6_5_1" (uses := "kerodon_1_1_0_6, kerodon_5_1_4_1, kerodon_8_6_5_8, kerodon_8_6_5_18")
Kerodon Theorem 8.6.5.1（[Tag 04DT](https://kerodon.net/tag/04DT)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：左ファイブレーションの通常圏上の再構成の逆圏比較と、重み付き神経の余カルテシアン性を確認した。任意の底上で各ファイバーを反転する双対の存在と底上の同値による一意性は未確認。

:::

:::corollary "kerodon_8_6_5_2" (uses := "kerodon_1_1_0_6, kerodon_5_1_4_1, kerodon_8_6_5_1")
Kerodon Corollary 8.6.5.2（[Tag 04DU](https://kerodon.net/tag/04DU)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：左右のファイブレーションを底ごと反転する既存の圏同値はある。余カルテシアン射を同じ底のまま保つ双対化で同値類に全単射を作る宣言は確認できない。

:::

:::definition "kerodon_8_6_5_3"
Kerodon Variant 8.6.5.3（[Tag 04DV](https://kerodon.net/tag/04DV)）。対応表の状態：なし。

cartesian fibrationの全反転で得るcocartesian fibrationは、原文の底を固定してファイバーだけ反転するdualityとは異なる構成。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cartesianFibration_op_toCocartesianHornFibration`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCartesianEdge_iff_isCocartesianEdge_op`

:::

:::definition "kerodon_8_6_5_6" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_5_8_1, kerodon_5_1_4_1")
Kerodon Construction 8.6.5.6（[Tag 04DY](https://kerodon.net/tag/04DY)）。対応表の状態：なし。

固定宇宙の空間値分類は、原文の指定された数値κのS\_\<κ値関手の相対指数と比較する型を含まない。一般の相対指数の補題だけをその同値としない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHom`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.fiberwiseHomFiberIso`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.IsCorepresentableSmallSpaceFunctor`

:::

:::proposition "kerodon_8_6_5_8" (uses := "kerodon_1_1_0_6, kerodon_4_9_8_2, kerodon_5_1_4_1, kerodon_8_3_2_21, kerodon_8_6_4_12, kerodon_8_6_4_13, kerodon_8_6_5_12, kerodon_8_6_5_15")
Kerodon Proposition 8.6.5.8（[Tag 04E0](https://kerodon.net/tag/04E0)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：単独の準圏の余米田の評価と相対指数の転置はある。S\_\{\<κ\} に値を取り、相対指数の余表現可能な部分の評価がファイブレーションの双対となる結果は未確認。

:::

:::proposition "kerodon_8_6_5_9" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_5_1_4_1, kerodon_5_3_6_9, kerodon_5_3_6_10, kerodon_6_2_5_7, kerodon_7_3_6_3, kerodon_7_6_6_19")
Kerodon Proposition 8.6.5.9（[Tag 04E1](https://kerodon.net/tag/04E1)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：余カルテシアンな U と準圏 D から、原文と同じ射影のカルテシアン性と内ファイブレーション性は得られる。κ-小ささと D の κ-余完備性から逆向きの余カルテシアン性を示す宣言は未確認。

:::

:::definition "kerodon_8_6_5_11" (uses := "kerodon_1_4_0_1, kerodon_4_5_8_19, kerodon_5_1_1_1, kerodon_5_1_4_1, kerodon_7_3_7_9, kerodon_7_6_6_19")
Kerodon Variant 8.6.5.11（[Tag 04E3](https://kerodon.net/tag/04E3)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：左 Kan 拡張の局所判定と相対指数のカルテシアン辺のホーン判定を確認した。指数可能な U での余カルテシアン性と、Δ¹ 上の射の始点ファイバーからの左 Kan 拡張による余カルテシアン辺判定は未確認。

:::

:::proposition "kerodon_8_6_5_12" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_5_1_1_1, kerodon_5_1_4_1, kerodon_5_1_4_17, kerodon_5_3_6_9, kerodon_7_4_3_8, kerodon_8_3_1_9, kerodon_8_6_5_9")
Kerodon Proposition 8.6.5.12（[Tag 04E4](https://kerodon.net/tag/04E4)）。対応表の状態：なし。

同じ指定κ値の相対指数とEのファイバーの比較は引用にない。固定宇宙の分類と混同しない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.fiberwiseHomProjection_cartesianFibration`

:::

:::lemma_ "kerodon_8_6_5_13" (uses := "kerodon_1_4_0_1, kerodon_7_3_8_24, kerodon_8_3_1_7")
Kerodon Lemma 8.6.5.13（[Tag 04E5](https://kerodon.net/tag/04E5)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：余表現可能性を同値な全定義域へ移す宣言と左 Kan 拡張判定を確認した。任意の全部分圏への制限が同じ頂点 η により余表現され、かつ全域が左 Kan 拡張であることとの同値は未確認。

:::

:::lemma_ "kerodon_8_6_5_14" (uses := "kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_5_1_1_1, kerodon_5_1_2_3, kerodon_8_6_5_13")
Kerodon Lemma 8.6.5.14（[Tag 04E6](https://kerodon.net/tag/04E6)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：余米田の頂点、輸送の一意性、左 Kan 拡張判定を確認した。U の余カルテシアン辺で η を送る操作が二つのファイバーの余表現と全域の左 Kan 拡張を結ぶ三条件は未確認。

:::

:::lemma_ "kerodon_8_6_5_15" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_5_1_1_1, kerodon_5_1_4_1, kerodon_8_6_5_11, kerodon_8_6_5_14")
Kerodon Lemma 8.6.5.15（[Tag 04E7](https://kerodon.net/tag/04E7)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：既存の相対指数の辺判定はカルテシアン辺用。原文の余カルテシアン辺を、U の持ち上げによる余普遍頂点保存の存在条件・全称条件で判定する宣言は確認できない。

:::

:::definition "kerodon_8_6_5_16" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_5_1_1_1, kerodon_5_1_4_1, kerodon_8_3_2_9")
Kerodon Definition 8.6.5.16（[Tag 04E8](https://kerodon.net/tag/04E8)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：一つの空間値関手の余表現可能性と一般の余カルテシアン輸送はある。二つの射のファイバー積で余表現可能な pairing を作り、同じ底辺上の二つの持ち上げで余普遍頂点を保存する定義は未確認。

:::

:::proposition "kerodon_8_6_5_18" (uses := "kerodon_1_1_0_6, kerodon_5_1_1_1, kerodon_5_1_4_1, kerodon_5_1_7_15, kerodon_8_6_5_12, kerodon_8_6_5_15")
Kerodon Proposition 8.6.5.18（[Tag 04EA](https://kerodon.net/tag/04EA)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：相対指数の転置と固定した指定辺の保存述語はある。Fun\^\{corep\} への因子化、辺保存、底上での圏同値をそれぞれ弱い族・族・双対性に対応させる三つの同値は未確認。

:::

:::corollary "kerodon_8_6_5_19"
Kerodon Corollary 8.6.5.19（[Tag 04EB](https://kerodon.net/tag/04EB)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：単独の準圏の余米田の充満忠実性と相対指数の転置はある。K との合成の充満忠実性・弱い族による本質像・辺保存および同値の判定をまとめた原文の結果は確認できない。

:::

# 8.6.6 Comparison of Dual and Conjugate Fibrations

%%%
number := false
tag := "kerodon-8-6-6"
%%%

Kerodon [Tag 04ET](https://kerodon.net/tag/04ET)

:::proposition "kerodon_8_6_6_1" (uses := "kerodon_1_1_0_6, kerodon_5_1_4_1, kerodon_8_6_3_14, kerodon_8_6_5_1, kerodon_8_6_5_18, kerodon_8_6_6_14")
Kerodon Proposition 8.6.6.1（[Tag 04EU](https://kerodon.net/tag/04EU)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：逆圏で辺の向きとカルテシアン性を変える型、および相対 Tw の射を確認した。balanced coupling を使う双対と T を使う共役の必要十分条件は未確認。

:::

:::corollary "kerodon_8_6_6_2"
Kerodon Corollary 8.6.6.2（[Tag 04EV](https://kerodon.net/tag/04EV)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：逆圏で Tw の両射影が交換されることと、各辺のカルテシアン・余カルテシアン性の比較はある。二つのファイブレーションの共役を同時反転で交換する iff は未確認。

:::

:::corollary "kerodon_8_6_6_3" (uses := "kerodon_1_1_0_6, kerodon_5_1_4_1, kerodon_8_6_5_2, kerodon_8_6_6_1")
Kerodon Corollary 8.6.6.3（[Tag 05JR](https://kerodon.net/tag/05JR)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：既存の逆圏同値は左と右のファイブレーション用。任意の余カルテシアン射と Cᵒᵖ 上のカルテシアン射の同値類の間に、ファイバーを保持する共役で全単射を作る結果は未確認。

:::

:::corollary "kerodon_8_6_6_5"
Kerodon Corollary 8.6.6.5（[Tag 05JT](https://kerodon.net/tag/05JT)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常の span の双圏と、指定辺を余カルテシアン辺に送る関手の部分圏はある。左脚を U-余カルテシアン辺に制限した Cospan の C への引戻しのファイブレーション性と双対性は未確認。

:::

:::definition "kerodon_8_6_6_7" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowFunctorComparison, SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowFunctorComparison_isPrecompositionEquivalence, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation") (uses := "kerodon_1_1_0_6, kerodon_5_6_5_1, kerodon_8_1_1_15")
Kerodon Definition 8.6.6.7（[Tag 05JU](https://kerodon.net/tag/05JU)）。対応表の状態：一部。

*主張*　内部ファイブレーション $`U:E\to C` の非可算基数 $`\kappa` に対する相対 Hom 関手とは、$`\operatorname{Tw}(E)` から $`E^{\mathrm{op}}\times_{C^{\mathrm{op}}}\operatorname{Tw}(C)\times_C E` への左ファイブレーションの、$`\kappa`-小空間値の共変移送表現である。

twistedArrowFunctorComparison Uは、Tw(E)からTw(C)をEop×Eへ引き戻した対象への同じ比較λを直接構成する。指定Hの左輸送表現という条件全体は含まない。

:::

:::definition "kerodon_8_6_6_12" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomEquiv, SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowFunctorComparison") (uses := "kerodon_1_1_0_6, kerodon_4_5_8_1")
Kerodon Notation 8.6.6.12（[Tag 05JZ](https://kerodon.net/tag/05JZ)）。対応表の状態：一部。

*主張*　内部ファイブレーション $`E\to C` の $`\kappa`-小空間値相対 Hom 関手を、$`E` 側の変数で相対指数対象へ転置する。得られる $`E^{\mathrm{op}}\times_{C^{\mathrm{op}}}\operatorname{Tw}(C)\to\operatorname{Fun}(E/C,S_{<\kappa})` を相対 Yoneda 埋め込みと呼ぶ。

一般のfiberwiseHomEquivを同じ評価射の引戻し図式へ適用すると、原文の相対指数への転置Tという射の構成を直接与える。Hが空間値Homの場合のYonedaという追加同定は含まない。

:::

:::theorem "kerodon_8_6_6_14" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_5_1_1_1, kerodon_5_1_2_3, kerodon_5_1_4_1, kerodon_8_3_3_13, kerodon_8_6_1_13, kerodon_8_6_5_6, kerodon_8_6_5_11, kerodon_8_6_5_13, kerodon_8_6_5_14, kerodon_8_6_6_12")
Kerodon Theorem 8.6.6.14（[Tag 05K1](https://kerodon.net/tag/05K1)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：単独の準圏での余米田の充満忠実性と相対指数の転置はある。相対余米田の像が各ファイバーで余表現可能で、かつ Uᵒᵖ の共役を与える二結論は未確認。

:::

# 8.6.7 The Opposition Functor

%%%
number := false
tag := "kerodon-8-6-7"
%%%

Kerodon [Tag 04F8](https://kerodon.net/tag/04F8)

:::definition "kerodon_8_6_7_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.ConjugateAndDualFibrations.EdgewiseEnrichedObject, SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.ConjugateAndDualFibrations.edgewiseEnrichedObject_simplicialCategory, SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.ConjugateAndDualFibrations.edgewiseEnrichedComposition, SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.edgewiseEnrichedRight")
Kerodon Notation 8.6.7.1（[Tag 04F9](https://kerodon.net/tag/04F9)）。対応表の状態：本体にある。

*主張*　単体圏 $`E` に対し、同じ対象を持ち、各射単体集合をねじれ矢印単体集合に置き換えた $`E^{\asymp}` を作る。合成はねじれ矢印関手を合成に適用して定め、終域射影は忘却単体関手 $`E^{\asymp}\to E` を与える。

仮定：単体的圏 E を与える（Kerodon と一致）。結論：対象を自明な部分型で保持し、各 Hom に Tw を取り、元の合成から豊穣合成を定め、右端射影を豊穣関手として与える（一致）。

:::

:::proposition "kerodon_8_6_7_2" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.ConjugateAndDualFibrations.edgewiseEnrichedObject_sHom_kanComplex, SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.edgewiseEnrichedRight, SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight_trivialKanFibration, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration, SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence.isWeakHomotopyEquivalence, SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.edgewiseEnrichedInfinityMap_isQCatEquivalence")
Kerodon Proposition 8.6.7.2（[Tag 04FA](https://kerodon.net/tag/04FA)）。対応表の状態：本体にある。

*主張*　局所 Kan な単体圏 $`E` に対し $`E^{\asymp}` は局所 Kan であり、忘却関手 $`E^{\asymp}\to E` は単体圏の弱同値である。これはホモトピー整合神経の間に無限圏の同値を誘導する。

仮定：E の全ての豊穣 Hom は Kan（Kerodon と一致）。結論：edgewise 圏の局所 Kan 性と coherent nerve の同値を直接得る。豊穣射の弱同値は、対象射影が全射で、各 Hom の右端が自明 Kan ファイブレーションなので弱ホモトピー同値となることから得る（一致）。

:::

:::definition "kerodon_8_6_7_4" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat")
Kerodon Construction 8.6.7.4（[Tag 04FC](https://kerodon.net/tag/04FC)）。対応表の状態：一部。

*主張*　小さい無限圏を対象とし関手圏の芯を射空間とする単体圏 $`\operatorname{QCat}` に、8.6.7.1 の射空間ごとのねじれ矢印構成を施す。そのホモトピー整合神経を $`\mathcal{QC}^{\asymp}` と書く。

QCatとCatInfinityは原文の最初の入力である小準圏の豊穣圏とその脈体を直接構成する。twisted Homを使うQCat\^asympと比較πは含まない。

:::

:::proposition "kerodon_8_6_7_5" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.edgewiseEnrichedInfinityMap_isQCatEquivalence, SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.ConjugateAndDualFibrations.edgewiseEnrichedObject_sHom_kanComplex, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catInfinity_quasicategory")
Kerodon Proposition 8.6.7.5（[Tag 04FD](https://kerodon.net/tag/04FD)）。対応表の状態：本体にある。

*主張*　$`\mathcal{QC}^{\asymp}` は無限圏であり、忘却単体関手 $`\operatorname{QCat}^{\asymp}\to\operatorname{QCat}` から得られる $`\mathcal{QC}^{\asymp}\to\mathcal{QC}` は無限圏の同値である。

仮定：局所 Kan な豊穣圏 QCat を使う（Kerodon と一致）。結論：QCat を Hom ごとに edgewise 化した coherent nerve は準圏で、右端射影の coherent nerve が CatInfinity への圏同値となる（一致）。

:::

:::definition "kerodon_8_6_7_6"
Kerodon Construction 8.6.7.6（[Tag 04FE](https://kerodon.net/tag/04FE)）。対応表の状態：なし。

Kan複体だけのedgewise反転は、原文の全準圏を対象とするQCat\^asympの指定自己同型ではない。Spaceへの制限であっても指定σとの比較がない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseOppositeKanEnriched`、`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseOppositeKanInfinityMap`、`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseKanOppositeInfinityComparisonIso`

:::

:::proposition "kerodon_8_6_7_7"
Kerodon Proposition 8.6.7.7（[Tag 04FF](https://kerodon.net/tag/04FF)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の Kan 対象の反転と、Kan の coherent な反転図式はある。QCat 全体の通常の神経から CatInfinity への縦辺を持つ反転の可換正方形は未確認。

:::

:::proposition "kerodon_8_6_7_9"
Kerodon Proposition 8.6.7.9（[Tag 04FH](https://kerodon.net/tag/04FH)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：単体的集合の射を逆圏で移したときの同値性と、Kan の反転図式の同値はある。CatInfinity 自己関手 σ の二乗が恒等と関手同型になる型は未確認。

:::

:::proposition "kerodon_8_6_7_11"
Kerodon Proposition 8.6.7.11（[Tag 04FK](https://kerodon.net/tag/04FK)）。対応表の状態：なし。

空間のedgewise共通解像上の比較はあるが、原文のCatInfinity上の指定σを制限した関手との同一視を含まない。別の射同士の同型としてnone。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseKanOppositeInfinityComparisonIso`、`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseOppositeKanInfinityEquivalence`

:::

:::proposition "kerodon_8_6_7_12"
Kerodon Proposition 8.6.7.12（[Tag 04FL](https://kerodon.net/tag/04FL)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：空間値図式の反転と、左・右ファイブレーションの比較はある。任意の余カルテシアン双対を、CatInfinity 値の coherent 輸送表示の σ との後合成で特徴付ける iff は未確認。

:::

# 8.6.8 Contravariant Transport Representations

%%%
number := false
tag := "kerodon-8-6-8"
%%%

Kerodon [Tag 05WD](https://kerodon.net/tag/05WD)

:::definition "kerodon_8_6_8_1"
Kerodon Definition 8.6.8.1（[Tag 019V](https://kerodon.net/tag/019V)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：反変の辺輸送はカルテシアン射から構成される。全体の表示は左・右ファイブレーションと空間値について確認した。一般の E→C を Cᵒᵖ 上の CatInfinity 値図式の共役として表す述語は未確認。

:::

:::proposition "kerodon_8_6_8_3" (uses := "kerodon_1_1_0_6, kerodon_5_1_4_1, kerodon_5_6_0_2, kerodon_8_6_6_3")
Kerodon Proposition 8.6.8.3（[Tag 05WF](https://kerodon.net/tag/05WF)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：空間値の右ファイブレーションの逆圏比較と有限単体上の余カルテシアン straightening がある。ファイル名の cartesian extension は左ファイブレーションの引戻し正方形による表示の延長であり、一般のカルテシアン射の存在・一意性・全単射は未確認。

:::

:::definition "kerodon_8_6_8_4"
Kerodon Variant 8.6.8.4（[Tag 05WG](https://kerodon.net/tag/05WG)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：固定した宇宙の CatInfinity と、小ささを使う空間値左ファイブレーションの表示を確認した。任意の非可算 κ で QC\_\{\<κ\} 値の表示が存在する条件および同値類の全単射は未確認。

:::

:::definition "kerodon_8_6_8_5"
Kerodon Notation 8.6.8.5（[Tag 05WH](https://kerodon.net/tag/05WH)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：CatInfinity 値の関手圏と辺の反変輸送はある。一般のカルテシアン射を Fun(Cᵒᵖ,QC) の関手同型類として割り当てる全体の表示は未確認。

:::

:::proposition "kerodon_8_6_8_11"
Kerodon Proposition 8.6.8.11（[Tag 05WM](https://kerodon.net/tag/05WM)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：反変辺輸送の証拠、余カルテシアン側の straightening の頂点、および共変輸送の確認を行った。任意の T で両端のファイバーと F の値を結ぶ二つの関手同型正方形は未確認。

:::

:::corollary "kerodon_8_6_8_12"
Kerodon Corollary 8.6.8.12（[Tag 05WN](https://kerodon.net/tag/05WN)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：共変のホモトピー輸送とカルテシアン射の各辺の反変輸送はある。Cᵒᵖ→QC をホモトピー圏に降ろすと指定された反変ホモトピー輸送と同型になる型は未確認。

:::

:::proposition "kerodon_8_6_8_13"
Kerodon Proposition 8.6.8.13（[Tag 05WP](https://kerodon.net/tag/05WP)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：切断の core の厳密な極限比較と、左ファイブレーションの切断の同定を確認した。一般のカルテシアン切断の全準圏が CatInfinity における反変輸送図式の極限になる結論は未確認。

:::

:::proposition "kerodon_8_6_8_15"
Kerodon Proposition 8.6.8.15（[Tag 06TU](https://kerodon.net/tag/06TU)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：単体添字の局所化と、特定の輸送模型の亜群化を確認した。一般のカルテシアン辺だけを反転した全空間を CatInfinity における反変輸送図式の余極限とする型は未確認。

:::

:::proposition "kerodon_8_6_8_16"
Kerodon Proposition 8.6.8.16（[Tag 05WR](https://kerodon.net/tag/05WR)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：余カルテシアン切断の制限、左ファイブレーションの切断、および初期頂点評価の同値を確認した。C▷ 上の反変輸送が極限であることとカルテシアン切断の制限の同値との iff は未確認。

:::

:::definition "kerodon_8_6_8_17"
Kerodon Notation 8.6.8.17（[Tag 05WS](https://kerodon.net/tag/05WS)）。対応表の状態：なし。

CatInfinityだけでは原文の左右随伴の辺を選ぶ二つの非充満部分圏を構成しない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity`

:::

:::definition "kerodon_8_6_8_19"
Kerodon Construction 8.6.8.19（[Tag 05WU](https://kerodon.net/tag/05WU)）。対応表の状態：なし。

固定したpresentable二対象間のFunL(C,D)opとFunR(D,C)の同値は、原文のQC\_LAdj全体上で対象と射を動かす指定Ψではない。固定対象でのmatesを全体の関手と数えない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pairRightAdjointFunctor`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.presentableAdjointFunctorEquivalence_adjunction`

:::

:::proposition "kerodon_8_6_8_22"
Kerodon Proposition 8.6.8.22（[Tag 05WX](https://kerodon.net/tag/05WX)）。対応表の状態：なし。

固定二対象間の随伴関手の同値と自然変換のmatesは、原文の準圏そのものを対象とする全QC\_LAdjop→QC\_RAdjのΨの同値とは別の射。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.presentableAdjointFunctorEquivalence`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.presentableAdjointFunctorEquivalence_adjunction`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.adjointTransformationEquivalence`

:::

# 8.6.9 Coends of ∞-Categories

%%%
number := false
tag := "kerodon-8-6-9"
%%%

Kerodon [Tag 06TV](https://kerodon.net/tag/06TV)

:::proposition "kerodon_8_6_9_1"
Kerodon Proposition 8.6.9.1（[Tag 04CY](https://kerodon.net/tag/04CY)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：一般の局所化述語と、単体添字圏からの特定の射の局所化、および内アノダイン底変換の比較はある。任意の C′ 上でカルテシアンかつ C′ への像が退化する辺を反転する T′ の普遍性は未確認。

:::

:::corollary "kerodon_8_6_9_2"
Kerodon Corollary 8.6.9.2（[Tag 04EW](https://kerodon.net/tag/04EW)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：指定した W について局所化を定義する構成と相対 Tw の射はある。カルテシアン脚と退化した終点を持つ W の局所化で T を共役として特徴付ける二方向は未確認。

:::

:::corollary "kerodon_8_6_9_3"
Kerodon Corollary 8.6.9.3（[Tag 05WC](https://kerodon.net/tag/05WC)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：余カルテシアン辺を保つ相対関手の全部分圏はある。二つの共役 T₀,T を使う前・後合成の充満忠実性と、両側の辺保存による像の比較は未確認。

:::

:::definition "kerodon_8_6_9_5"
Kerodon Definition 8.6.9.5（[Tag 06TW](https://kerodon.net/tag/06TW)）。対応表の状態：なし。

通常圏のmulticoequalizerで定義するcoendは原文のTw(C)opを添字とする∞圏の余極限とは異なる図式。比較を引用に持たない。

宣言：`CategoryTheory.Limits.coend`

:::

:::definition "kerodon_8_6_9_6"
Kerodon Notation 8.6.9.6（[Tag 06TX](https://kerodon.net/tag/06TX)）。対応表の状態：なし。

通常圏添字のcoendFunctorは原文の∞圏の指定coendの高次関手性を返さない。

宣言：`CategoryTheory.Limits.coendFunctor`、`CategoryTheory.Limits.coend.map`

:::

:::theorem "kerodon_8_6_9_9"
Kerodon Theorem 8.6.9.9（[Tag 06U0](https://kerodon.net/tag/06U0)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏添字の単体集合の重み付き coend と辺の局所化はある。二つの輸送の CatInfinity 値 coend を、両脚が指定の持ち上げ辺である W で全空間の引戻しを局所化して求める型は未確認。

:::

:::corollary "kerodon_8_6_9_11"
Kerodon Corollary 8.6.9.11（[Tag 06U2](https://kerodon.net/tag/06U2)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：厳密な重み付き模型の引戻しの同型と通常圏添字の coend の普遍性、亜群化比較を確認した。任意の左・右ファイブレーションの引戻しと空間 coend との弱ホモトピー同値による必要十分条件は未確認。

:::

:::corollary "kerodon_8_6_9_12"
Kerodon Corollary 8.6.9.12（[Tag 06U3](https://kerodon.net/tag/06U3)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：単体添字模型の局所化は始点を保つ辺を使い、重み付き余極限は通常圏添字の厳密な構成。原文の Δ 上のカルテシアン射で最終頂点を保つ辺を反転して CatInfinity 値の coend を得る比較は未確認。

:::

