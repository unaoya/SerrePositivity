-- audit2: 7d0968dad3e8672a6213dc0e508983c17f14eaaa inputs sha256 b3e2631992a041109ef8ab3a4836cc24453830556fb4a9c55f9a166f68e2cde1
-- audit2 baselines: 23cbebdfe9d75717f3f248bb0069ebd9dc9bbef6, cddf4d2dac6a409e64204686cf743e703350a6f6
import Verso
import VersoManual
import VersoBlueprint
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PullbackTransport
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.LeftFibration
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.Projection

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "8.2 Couplings of ∞-Categories" =>
%%%
number := false
tag := "kerodon-8-2"
%%%

Kerodon の 8.2 節（[Tag 043P](https://kerodon.net/tag/043P)）の項目と、SerrePositivity・Mathlib の宣言との対応。本文は対応表（research/kerodon-coverage）の判定の理由の要約で、Kerodon の本文の写しではない。

:::definition "kerodon_8_2_0_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection_leftFibration, SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration") (uses := "kerodon_1_4_0_1")
Kerodon Definition 8.2.0.1（[Tag 043Q](https://kerodon.net/tag/043Q)）。対応表の状態：本体にある。

*主張*　無限圏 $`C_+` と $`C_-` の coupling は、無限圏 $`C` と左ファイブレーション $`C\to C_-^{\mathrm{op}}\times C_+` のデータである。

準圏Cとλ:C→C₋ᵒᵖ⊗C₊にLeftFibration λを指定した組が原文のcouplingの定義そのもの。LeftFibrationと積の型を追記し、専用のCouplingという構造名の欠如だけはpartialの理由にしない。

:::

:::definition "kerodon_8_2_0_3" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection_leftFibration, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibration_pullback_snd") (uses := "kerodon_1_4_0_1, kerodon_8_1_1_11")
Kerodon Construction 8.2.0.3（[Tag 043S](https://kerodon.net/tag/043S)）。対応表の状態：一部。

*主張*　無限圏の関手 $`G:C_+\to C_-` に対応する coupling は、ねじれ矢印の左ファイブレーションを $`\mathrm{id}\times G` に沿って引き戻した $`\operatorname{Tw}(C_-)\times_{C_-}C_+\to C_-^{\mathrm{op}}\times C_+` である。

twistedArrowProjection C₋をid⊗Gに沿って引き戻すと、leftFibration\_pullback\_sndは原文の同じpullback couplingのleft fibration性を直接与える。Tw(C₋)×\_\{C₋\}C₊への別表示の同型まではこの引用に含まない。

:::

:::theorem "kerodon_8_2_0_4" (uses := "kerodon_1_4_0_1, kerodon_8_2_0_3")
Kerodon Theorem 8.2.0.4（[Tag 043T](https://kerodon.net/tag/043T)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Yoneda の充満忠実性と一つの終点における表現可能ファイブレーションの比較はある。全代表可能 coupling の同値類を関手の同型類と対応させる全単射は見つからない。

:::

# 8.2.1 Representable Couplings

%%%
number := false
tag := "kerodon-8-2-1"
%%%

Kerodon [Tag 043X](https://kerodon.net/tag/043X)

:::definition "kerodon_8_2_1_1" (uses := "kerodon_1_4_0_1")
Kerodon Definition 8.2.1.1（[Tag 043Y](https://kerodon.net/tag/043Y)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：準圏の初期頂点と Tw の特定の始域ファイバーでの恒等射の初期性はある。任意の coupling で片方の射影のファイバーに初期性を課す二つの定義は見つからない。

:::

:::definition "kerodon_8_2_1_3" (uses := "kerodon_1_4_0_1")
Kerodon Definition 8.2.1.3（[Tag 0440](https://kerodon.net/tag/0440)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：始域固定の Tw で初期対象を得る補題と終点固定の表現可能模型はある。任意の左ファイブレーションで、片方の座標の各頂点のファイバーに初期対象があることを要求する二つの述語は見つからない。

:::

:::definition "kerodon_8_2_1_6"
Kerodon Variant 8.2.1.6（[Tag 0443](https://kerodon.net/tag/0443)）。対応表の状態：なし。

固定終点のTw fiberと反転sliceの比較、および恒等射の終対象性はあるが、原文の任意Gのcouplingで普遍対象がeの可逆性と同値という判定を直接返さない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.rightRepresentableTwistedArrowMap_isQCatEquivalence`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceIdentityCone_isTerminalVertex`

:::

:::proposition "kerodon_8_2_1_7" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_5_1_1_1, kerodon_5_1_1_9, kerodon_5_1_4_1, kerodon_5_1_4_13, kerodon_5_1_4_14, kerodon_5_1_4_15")
Kerodon Proposition 8.2.1.7（[Tag 0444](https://kerodon.net/tag/0444)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：単一の左ファイブレーションを全辺 cocartesian の条件で判定する iff はある。二射影のそれぞれの cocartesian 辺を反対側の座標の可逆性で判定し、joint な isofibration と組み合わせる iff は見つからない。

:::

:::proposition "kerodon_8_2_1_8" (uses := "kerodon_1_4_0_1, kerodon_4_5_8_1, kerodon_4_5_8_18, kerodon_5_1_1_1, kerodon_5_1_4_1, kerodon_5_1_4_9, kerodon_5_3_6_1, kerodon_6_2_5_1, kerodon_6_2_5_2, kerodon_7_3_5_7, kerodon_7_3_5_9, kerodon_7_3_6_11, kerodon_7_3_7_6, kerodon_8_2_1_7")
Kerodon Proposition 8.2.1.8（[Tag 0445](https://kerodon.net/tag/0445)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：単独の初期頂点の評価から全辺で cocartesian な図式を延ばせる。corepresentable coupling 上の相対関手圏で初期対象を作り、全 couniversal 頂点の像と辺保存で初期性を判定する型は見つからない。

:::

:::corollary "kerodon_8_2_1_10"
Kerodon Corollary 8.2.1.10（[Tag 0447](https://kerodon.net/tag/0447)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Tw の始域ファイバーでの恒等射の初期性と、初期頂点からの cocartesian 延長はある。Tw(C) 全体上の相対関手圏での初期対象と、全恒等射および指定辺による特徴づけは見つからない。

:::

# 8.2.2 Morphisms of Couplings

%%%
number := false
tag := "kerodon-8-2-2"
%%%

Kerodon [Tag 0448](https://kerodon.net/tag/0448)

:::definition "kerodon_8_2_2_1"
Kerodon Definition 8.2.2.1（[Tag 0449](https://kerodon.net/tag/0449)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：固定した一つの底写像への相対関手空間はある。負側と正側の底関手も動かす三つ組を、二つの制限の引き戻しで表す構成は見つからない。

:::

:::proposition "kerodon_8_2_2_2" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_2_5_2")
Kerodon Proposition 8.2.2.2（[Tag 044A](https://kerodon.net/tag/044A)）。対応表の状態：なし。

内部HomのpullbackObjObjπのleft fibration性は、両側可変のFun±から二関手空間への指定射と同じ射にするpullback比較がない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibration_pullbackObjObjπ`

:::

:::corollary "kerodon_8_2_2_5"
Kerodon Corollary 8.2.2.5（[Tag 044D](https://kerodon.net/tag/044D)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：一つの左ファイブレーションの固定底の相対関手空間には Kan 性がある。両側の底関手を動かす Fun±(C,D) の準圏性を述べる型は見つからない。

:::

:::proposition "kerodon_8_2_2_9" (uses := "kerodon_1_4_0_1, kerodon_4_2_5_2, kerodon_4_5_3_22, kerodon_4_5_3_28, kerodon_5_1_1_1, kerodon_5_1_4_1, kerodon_5_2_1_1, kerodon_6_3_1_1, kerodon_6_3_4_3, kerodon_8_2_1_7")
Kerodon Proposition 8.2.2.9（[Tag 044F](https://kerodon.net/tag/044F)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：同じ底上の左ファイブレーション間の同値をファイバーで判定する型と余終性の基底変更はある。一方または両方の座標ファイバーが弱可縮のとき、指定の忘却関手を辺保存の全部分圏への同値とする三結論は見つからない。

:::

:::corollary "kerodon_8_2_2_10" (uses := "kerodon_1_4_0_1, kerodon_4_5_3_19, kerodon_4_5_3_22, kerodon_4_5_3_28, kerodon_5_1_1_1, kerodon_5_1_4_1, kerodon_5_2_1_1, kerodon_8_2_1_7, kerodon_8_2_2_9")
Kerodon Corollary 8.2.2.10（[Tag 044H](https://kerodon.net/tag/044H)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：固定底で (co)cartesian な辺の保存を要求する構成と左 straightening の相対比較はある。正側の F₊ を固定したときの Fun± からの忘却の充満忠実性と、辺保存による像の特徴づけは見つからない。

:::

:::theorem "kerodon_8_2_2_11" (uses := "kerodon_1_4_0_1, kerodon_5_1_1_1, kerodon_5_1_4_1, kerodon_5_3_1_10, kerodon_8_2_1_7, kerodon_8_2_1_8, kerodon_8_2_2_10")
Kerodon Theorem 8.2.2.11（[Tag 044K](https://kerodon.net/tag/044K)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：個別の Tw ファイバーの初期頂点と相対内部 Hom の左ファイブレーション性はある。表現可能な λ と余表現可能な μ に対する Fun± の余表現可能性、および普遍対象から余普遍対象への移送での判定は見つからない。

:::

:::corollary "kerodon_8_2_2_13" (uses := "kerodon_1_4_0_1, kerodon_4_4_5_6, kerodon_4_7_3_16, kerodon_8_2_2_11")
Kerodon Corollary 8.2.2.13（[Tag 044N](https://kerodon.net/tag/044N)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Tw の関手性は同じ F を両端に適用した四角形を与える。異なる F₋ と F₊ を端点に持ち可逆射を可逆射へ送る写像の存在と F₋≅F₊ の iff は見つからない。

:::

# 8.2.3 Representations of Couplings

%%%
number := false
tag := "kerodon-8-2-3"
%%%

Kerodon [Tag 044Q](https://kerodon.net/tag/044Q)

:::definition "kerodon_8_2_3_1" (uses := "kerodon_1_4_0_1, kerodon_8_2_0_3")
Kerodon Definition 8.2.3.1（[Tag 044R](https://kerodon.net/tag/044R)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：指定した終点の表現可能左ファイブレーションの比較はある。G を任意の正側準圏上で動かし、λ が joint な底上で λ\_G と同値であるとする述語は見つからない。

:::

:::theorem "kerodon_8_2_3_4" (uses := "kerodon_1_4_0_1, kerodon_8_2_1_3, kerodon_8_2_2_11, kerodon_8_2_3_1, kerodon_8_2_3_7")
Kerodon Theorem 8.2.3.4（[Tag 044U](https://kerodon.net/tag/044U)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：単独の終点での表現可能比較と Yoneda の充満忠実性はある。初期対象が各ファイバーにあるという入力から全体の G を構成して、その同型を除いた一意性を結論する型は見つからない。

:::

:::definition "kerodon_8_2_3_5" (uses := "kerodon_1_4_0_1")
Kerodon Definition 8.2.3.5（[Tag 044V](https://kerodon.net/tag/044V)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：左 straightening の基底変更と一つの終点の Tw への底上の比較を確認した。任意の G の id×G に沿う指定正方形の categorical pullback 性と λ の表現可能性を比較する型は見つからない。

:::

:::lemma_ "kerodon_8_2_3_6" (uses := "kerodon_1_4_0_1, kerodon_5_1_6_1, kerodon_5_6_6_20")
Kerodon Lemma 8.2.3.6（[Tag 044X](https://kerodon.net/tag/044X)）。対応表の状態：なし。

全ての二端点のfiberの同値による判定は原文の正側だけを固定したfiber全体の同値とは異なる。普遍対象保存という第三条件への比較もない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.leftFibration_isQCatEquivalence_iff_fibers`

:::

:::proposition "kerodon_8_2_3_7" (uses := "kerodon_1_4_0_1, kerodon_8_2_2_11, kerodon_8_2_3_1, kerodon_8_2_3_6")
Kerodon Proposition 8.2.3.7（[Tag 044Z](https://kerodon.net/tag/044Z)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：終点固定の Tw の表現可能模型と左ファイブレーションの同値のファイバー判定はある。指定 λ の普遍対象が可逆射へ移ること、および (id,G̃,G) の初期性まで含む四条件は見つからない。

:::

:::definition "kerodon_8_2_3_8"
Kerodon Variant 8.2.3.8（[Tag 0451](https://kerodon.net/tag/0451)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Tw の両端交換は反対圏との指定の底変換を保つ。Fᵒᵖ×id への任意の categorical pullback による余表現可能性と F の同型を除いた一意性は見つからない。

:::

:::proposition "kerodon_8_2_3_9" (uses := "kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_4_2_5_2, kerodon_4_5_3_30, kerodon_5_1_6_4, kerodon_8_2_2_2, kerodon_8_2_3_5, kerodon_8_2_3_7")
Kerodon Proposition 8.2.3.9（[Tag 0453](https://kerodon.net/tag/0453)）。対応表の状態：なし。

relativeFunctorIsPullbackIsoは底写像を一つ固定した相対関手空間の型。原文のFun±で負側も可変な条件(3)やcouplingの表現可能性への比較を含まない。

宣言：`SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeFunctorIsPullbackIso`、`SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace_kanComplex`

:::

# 8.2.4 Presentations of Representable Couplings

%%%
number := false
tag := "kerodon-8-2-4"
%%%

Kerodon [Tag 0455](https://kerodon.net/tag/0455)

:::definition "kerodon_8_2_4_1" (uses := "kerodon_1_4_0_1")
Kerodon Definition 8.2.4.1（[Tag 0456](https://kerodon.net/tag/0456)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：特定の Tw ファイバーで恒等射が初期となる型と底を保つ表現可能比較はある。Gᵒᵖ×id の上の Tw(C₊) からの写像について、全恒等頂点の像に普遍性を要求する述語は見つからない。

:::

:::proposition "kerodon_8_2_4_3" (uses := "kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_8_2_2_13, kerodon_8_2_3_1, kerodon_8_2_3_4, kerodon_8_2_3_5, kerodon_8_2_3_9, kerodon_8_2_4_1")
Kerodon Proposition 8.2.4.3（[Tag 0459](https://kerodon.net/tag/0459)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：底を固定した引き戻しから相対関手空間を比較する型と一つの終点での Tw の表現可能比較はある。λ\_G との同値を、全恒等頂点に条件を課す witness の存在に置き換える iff は見つからない。

:::

:::corollary "kerodon_8_2_4_4"
Kerodon Corollary 8.2.4.4（[Tag 045C](https://kerodon.net/tag/045C)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：同じ関手を Tw の両端に適用する自然性と Yoneda の充満忠実性はある。H∘F₊≅F₋∘G と、普遍対象を保つ coupling 写像の存在を往復する型は見つからない。

:::

:::definition "kerodon_8_2_4_5" (uses := "kerodon_1_4_0_1")
Kerodon Variant 8.2.4.5（[Tag 045G](https://kerodon.net/tag/045G)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Tw の両端交換と始域固定ファイバー内の恒等射の初期性はある。id×F の上の写像の恒等頂点の像で余表現を定義し、反対圏の表現条件と同定する型は見つからない。

:::

:::theorem "kerodon_8_2_4_6" (uses := "kerodon_1_4_0_1, kerodon_8_2_2_11, kerodon_8_2_3_7")
Kerodon Theorem 8.2.4.6（[Tag 045J](https://kerodon.net/tag/045J)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：一つの随伴に対する自然な Hom 比較と相対内部 Hom の左ファイブレーション性はある。Fun± の表現関手を T₊↦G∘T₊∘F とし、余普遍対象から普遍対象への移送で特徴づける型は見つからない。

:::

:::proposition "kerodon_8_2_4_9" (uses := "kerodon_1_4_0_1, kerodon_5_1_1_1, kerodon_5_1_4_1, kerodon_7_2_1_9, kerodon_7_2_3_14, kerodon_8_1_2_1, kerodon_8_2_1_7, kerodon_8_2_4_1")
Kerodon Proposition 8.2.4.9（[Tag 045P](https://kerodon.net/tag/045P)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：任意の写像の左余終性は slice の弱可縮性で判定でき、Tw の始域ファイバーの恒等射は初期となる。指定された Tw(C₊)→C の左余終性を恒等頂点または可逆頂点の像の普遍性で判定する型は見つからない。

:::

# 8.2.5 Adjunctions as Couplings

%%%
number := false
tag := "kerodon-8-2-5"
%%%

Kerodon [Tag 045R](https://kerodon.net/tag/045R)

:::theorem "kerodon_8_2_5_1" (uses := "kerodon_1_4_0_1, kerodon_6_2_1_1, kerodon_8_2_0_4, kerodon_8_2_2_11, kerodon_8_2_3_5, kerodon_8_2_3_7, kerodon_8_2_4_3, kerodon_8_2_4_5, kerodon_8_2_4_6, kerodon_8_2_5_2")
Kerodon Theorem 8.2.5.1（[Tag 045S](https://kerodon.net/tag/045S)）。対応表の状態：なし。

随伴から得る各xでの共変HomのFunctorIsoは、原文の指定coupling λを同じFがcorepresentする条件への比較を欠く。Homの同型だけをcouplingの結論と数えない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.CouplingsOfInfinityCategories.adjunctionCovariantHomIso`

:::

:::proposition "kerodon_8_2_5_2" (uses := "kerodon_1_4_0_1, kerodon_4_7_3_10, kerodon_6_2_6_2, kerodon_8_1_2_10")
Kerodon Proposition 8.2.5.2（[Tag 045T](https://kerodon.net/tag/045T)）。対応表の状態：なし。

exists\_leftAdjoint\_iff\_covariantHom\_representableは共変Hom関手の各xでの余表現可能性を判定する。原文の同じλのcorepresentabilityとの比較がないため、λ\_Gの場合も別の条件の類似だけと判定する。

宣言：`SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.exists_leftAdjoint_iff_covariantHom_representable`

:::

# 8.2.6 Balanced Couplings

%%%
number := false
tag := "kerodon-8-2-6"
%%%

Kerodon [Tag 045W](https://kerodon.net/tag/045W)

:::definition "kerodon_8_2_6_1" (uses := "kerodon_1_4_0_1")
Kerodon Definition 8.2.6.1（[Tag 045X](https://kerodon.net/tag/045X)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：随伴による二変数の表現比較と個別 Tw ファイバーの初期頂点はある。任意の coupling で両側の初期対象の存在と、その二種類の頂点条件の一致をまとめた述語は見つからない。

:::

:::theorem "kerodon_8_2_6_6"
Kerodon Theorem 8.2.6.6（[Tag 045Z](https://kerodon.net/tag/045Z)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：準圏の同値から随伴を作り、その随伴から Hom の自然同型を取れる。balanced 条件を、表現関手 G または余表現関手 F が準圏同値であることと往復する型は見つからない。

:::

:::corollary "kerodon_8_2_6_7"
Kerodon Corollary 8.2.6.7（[Tag 04AX](https://kerodon.net/tag/04AX)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：準圏同値から随伴を作る型と Tw の左ファイブレーションはある。任意の二準圏の同値を、それらを結ぶ balanced coupling の存在で判定する型は見つからない。

:::

:::corollary "kerodon_8_2_6_8"
Kerodon Corollary 8.2.6.8（[Tag 0460](https://kerodon.net/tag/0460)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Tw(Cᵒᵖ) と Tw(C) の底交換による引き戻しの同型はある。任意の balanced coupling を、両側の底同値と共に一つの Tw(D) へ移す iff は見つからない。

:::

:::proposition "kerodon_8_2_6_9"
Kerodon Proposition 8.2.6.9（[Tag 0461](https://kerodon.net/tag/0461)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：随伴を追加し h Fun での後合成を充満忠実と仮定すると余単位の可逆性が得られる。λ が表現可能という仮定だけで、全普遍対象の余普遍性と G の充満忠実性を往復する型は見つからない。

:::

