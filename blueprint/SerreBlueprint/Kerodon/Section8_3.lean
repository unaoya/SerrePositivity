import Verso
import VersoManual
import VersoBlueprint
import Mathlib.AlgebraicTopology.SimplicialSet.Basic
import Mathlib.CategoryTheory.Profunctor.Basic
import Mathlib.CategoryTheory.Yoneda
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PointedSpaces
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePath
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.YonedaInfinityConstruction

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "8.3 The Yoneda Embedding" =>
%%%
number := false
tag := "kerodon-8-3"
%%%

Kerodon の 8.3 節（[Tag 03LZ](https://kerodon.net/tag/03LZ)）の項目と、SerrePositivity・Mathlib の宣言との対応。本文は対応表（research/kerodon-coverage）の判定の理由の要約で、Kerodon の本文の写しではない。

:::proposition "kerodon_8_3_0_1" (lean := "CategoryTheory.Coyoneda.fullyFaithful")
Kerodon Proposition 8.3.0.1（[Tag 03M0](https://kerodon.net/tag/03M0)）。対応表の状態：Mathlib にある。

仮定：通常圏 C。Hom の宇宙を値域 Type に取る（Kerodon の局所小圏と一致）。結論：Coyoneda.fullyFaithful は Cᵒᵖ から共変表現可能関手を送る coyoneda の充満忠実性（原文と一致）。

:::

# 8.3.1 Yoneda's Lemma

%%%
number := false
tag := "kerodon-8-3-1"
%%%

Kerodon [Tag 03M2](https://kerodon.net/tag/03M2)

*定理 15.2 （Yoneda の補題）*

$`C` を小さい quasicategory とする。

:::proposition "kerodon_8_3_1_1" (lean := "CategoryTheory.coyonedaEquiv, CategoryTheory.yonedaEquiv")
Kerodon Proposition 8.3.1.1（[Tag 03M3](https://kerodon.net/tag/03M3)）。対応表の状態：Mathlib にある。

仮定：通常圏 C、対象 X、F : C⥤Type（Kerodon と一致）。結論：coyonedaEquiv は自然変換 hˣ→F と F(X) の同値で、順写像は X で恒等射を評価する（原文の全単射と一致）。

:::

:::definition "kerodon_8_3_1_2" (uses := "kerodon_1_4_0_1, kerodon_3_1_6_1, kerodon_4_6_8_15")
Kerodon Notation 8.3.1.2（[Tag 03M4](https://kerodon.net/tag/03M4)）。対応表の状態：なし。

SpaceInfinityの定義は原文の指定F,G,X,ηを入力に取らず、評価とηの前合成による同じ比較射を構成しない。値圏があるだけは構成成分としない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity`

:::

:::proposition "kerodon_8_3_1_3" (uses := "kerodon_1_4_0_1, kerodon_5_6_6_1, kerodon_7_3_6_1, kerodon_8_3_1_2, kerodon_8_3_1_7")
Kerodon Proposition 8.3.1.3（[Tag 03M5](https://kerodon.net/tag/03M5)）。対応表の状態：一部。

原文の圏を小準圏の反対圏、Fを標準representablePresheafInfinity、ηを恒等射の頂点に指定すると、yonedaPresheafEvaluation\_isQCatEquivalenceは同じ標準Yoneda評価の同値を直接返す。任意の(F,η)へは広げない。

*定理 15.2 （Yoneda の補題）*

- 前層 $`F`（定義 14.2）と頂点 $`y` について、$`\mathrm{Hom}^R_{\mathcal P(C)}(h_y,F)` と $`F(y)` はホモトピー同値である。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaPresheafEvaluation_isQCatEquivalence`、`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafInfinity`

:::

:::corollary "kerodon_8_3_1_6"
Kerodon Corollary 8.3.1.6（[Tag 03M8](https://kerodon.net/tag/03M8)）。対応表の状態：なし。

leftFibration\_exists\_initial\_of\_covariantRepresentationの結論は全空間の始対象の存在。原文の同じ指定ηによる三つの比較条件のいずれでもなく、必要十分条件の一部と数えない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.leftFibration_exists_initial_of_covariantRepresentation`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.covariantRepresentableInfinity`

:::

:::lemma_ "kerodon_8_3_1_7" (uses := "kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_5_6_6_1, kerodon_7_1_2_8, kerodon_7_3_1_5")
Kerodon Lemma 8.3.1.7（[Tag 03M9](https://kerodon.net/tag/03M9)）。対応表の状態：なし。

通常圏のYonedaMapの左Kan性は、原文の準圏の同じ指定ηのcorepresentationと一点からの左Kan性の比較を含まない。

宣言：`CategoryTheory.Presheaf.instIsLeftKanExtensionOppositeObjFunctorTypeYonedaYonedaMap`

:::

:::corollary "kerodon_8_3_1_8" (uses := "kerodon_1_4_0_1, kerodon_7_3_1_5, kerodon_7_3_8_24, kerodon_8_3_1_7")
Kerodon Corollary 8.3.1.8（[Tag 04B5](https://kerodon.net/tag/04B5)）。対応表の状態：なし。

MathlibのYonedaMapの指定左Kan変換は、原文の任意のβに沿う指定ηの像の余表現性との比較を欠く。

宣言：`CategoryTheory.Presheaf.instIsLeftKanExtensionOppositeObjFunctorTypeYonedaYonedaMap`

:::

:::corollary "kerodon_8_3_1_9" (uses := "kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_8_3_1_3, kerodon_8_3_1_8")
Kerodon Corollary 8.3.1.9（[Tag 04B6](https://kerodon.net/tag/04B6)）。対応表の状態：なし。

通常圏の表現可能前層の左Kan性は、原文の同じ空間値Gが余表現可能であることとのiffへ移すnerve比較を含まない。

宣言：`CategoryTheory.Presheaf.instIsLeftKanExtensionOppositeObjFunctorTypeYonedaYonedaMap`

:::

# 8.3.2 Profunctors of ∞-Categories

%%%
number := false
tag := "kerodon-8-3-2"
%%%

Kerodon [Tag 03MA](https://kerodon.net/tag/03MA)

:::definition "kerodon_8_3_2_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedArrowHomInfinity, CategoryTheory.Profunctor, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity") (uses := "kerodon_1_4_0_1")
Kerodon Definition 8.3.2.1（[Tag 03MB](https://kerodon.net/tag/03MB)）。対応表の状態：本体にある。

任意のC₋ᵒᵖ⊗C₊からSpaceInfinityへの単体射の型が原文のprofunctorそのもの。SpaceInfinityとfunctorVertexEquivによりこの全型を表せ、専用のProfunctor名の欠如はpartial理由にしない。Mathlibの通常圏のProfunctorは根拠にしない。

:::

:::definition "kerodon_8_3_2_6"
Kerodon Variant 8.3.2.6（[Tag 0465](https://kerodon.net/tag/0465)）。対応表の状態：なし。

固定宇宙のleft straighteningの同値は、原文の任意の非可算κで切った空間と本質的κ-smallなfiberという像の条件を型に含まない。宇宙をκの代用にしない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityEquivalence`

:::

:::definition "kerodon_8_3_2_7" (uses := "kerodon_1_2_5_1, kerodon_1_4_0_1")
Kerodon Definition 8.3.2.7（[Tag 0466](https://kerodon.net/tag/0466)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：ある頂点による余表現の存在述語と、余表現があるときの全空間の初期頂点の存在はある。K(X,Y) の指定 η が二つの部分評価のいずれを表現するかを定める一対の述語は見つからない。

:::

:::definition "kerodon_8_3_2_9" (uses := "kerodon_1_4_0_1, kerodon_5_6_6_1, kerodon_5_6_6_2")
Kerodon Definition 8.3.2.9（[Tag 03ME](https://kerodon.net/tag/03ME)）。対応表の状態：一部。

小空間値の図式については、各yで制限した図式にIsRepresentableSmallSpaceFunctor、各xでIsCorepresentableSmallSpaceFunctorを課すことが同じ二つの点ごとの定義を直接表す。型にある宇宙持ち上げを用いる範囲に限定し、任意の大きさの図式へは広げない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.IsRepresentableSmallSpaceFunctor`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.IsCorepresentableSmallSpaceFunctor`

:::

:::proposition "kerodon_8_3_2_17" (uses := "kerodon_1_4_0_1, kerodon_8_3_1_3")
Kerodon Proposition 8.3.2.17（[Tag 03ML](https://kerodon.net/tag/03ML)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：標準の co-Yoneda の充満忠実性と個別関手の余表現可能性はある。任意の余表現可能 profunctor のカリー化した関手の充満忠実性を、全余普遍頂点の普遍性で判定する iff は見つからない。

:::

:::definition "kerodon_8_3_2_18" (uses := "kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_8_3_2_9")
Kerodon Definition 8.3.2.18（[Tag 03MM](https://kerodon.net/tag/03MM)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：個々の空間値関手の表現可能・余表現可能の述語はある。二変数 K の各側の部分評価への存在条件と、同じ指定頂点での二つの普遍性の一致をまとめる述語は見つからない。

:::

:::corollary "kerodon_8_3_2_20" (uses := "kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_5_6_6_13, kerodon_8_3_2_17, kerodon_8_3_2_18")
Kerodon Corollary 8.3.2.20（[Tag 03MN](https://kerodon.net/tag/03MN)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：標準の二つの Yoneda 写像は充満忠実で、個別の表現可能性も定義される。任意の K に対して balanced、二つの currying の充満忠実性とそれぞれの本質像を結ぶ三条件の同値は見つからない。

:::

:::corollary "kerodon_8_3_2_21" (uses := "kerodon_1_4_0_1")
Kerodon Corollary 8.3.2.21（[Tag 03MP](https://kerodon.net/tag/03MP)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：元の C の二変数 Hom の評価と co-Yoneda の充満忠実性はある。余表現可能なすべての空間値関手の全部分圏との評価写像について balanced 条件を証明する型は見つからない。

:::

# 8.3.3 Hom-Functors for ∞-Categories

%%%
number := false
tag := "kerodon-8-3-3"
%%%

Kerodon [Tag 03MR](https://kerodon.net/tag/03MR)

*注意 （大きさ）*

$`\mathcal S` は小さくない（第 3 章の注意）ので、$`\mathcal P(C)` も小さくない単体的集合である。前層 $`F` の頂点 $`x` での値 $`F(x)` は $`\mathcal S` の頂点、つまり小さい Kan 複体である。

:::definition "kerodon_8_3_3_1" (uses := "kerodon_1_4_0_1")
Kerodon Definition 8.3.3.1（[Tag 046B](https://kerodon.net/tag/046B)）。対応表の状態：一部。

twistedArrowHomInfinityは原文のTw couplingの標準left straighteningを実際に構成し、一つのHom-functorの構成成分を直接与える。任意のHの輸送表現性という条件の全定義はこの宣言だけに含まない。

*定義 12.5 （関手 $`\mathrm{Map}_C`）*

$`C` を小さい quasicategory とする。定理 12.4 と上の注意により、射影 $`\mathrm{Tw}(C)\to C^{\mathrm{op}}\times C` は小さいファイバーをもつ左 fibration なので、その straightening（定義 11.3）

$$`\mathrm{Map}_C=\mathrm{St}\bigl(\mathrm{Tw}(C)\to C^{\mathrm{op}}\times C\bigr)\colon C^{\mathrm{op}}\times C\to\mathcal S`

を $`C` の写像空間の関手と定める。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedArrowHomInfinity`

:::

:::proposition "kerodon_8_3_3_2" (uses := "kerodon_1_4_0_1, kerodon_5_6_0_6")
Kerodon Proposition 8.3.3.2（[Tag 03N2](https://kerodon.net/tag/03N2)）。対応表の状態：一部。

Cを宇宙で小さく標準Hom-functorを指定するとtwistedArrowHomInfinityはその存在を直接与える。一般の局所小性からのiffと任意のHの一意性は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedArrowHomInfinity`、`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.homInfinityJointEvaluation`

:::

:::definition "kerodon_8_3_3_5"
Kerodon Variant 8.3.3.5（[Tag 03V2](https://kerodon.net/tag/03V2)）。対応表の状態：なし。

SpaceInfinityの宇宙パラメータだけでは、原文の特定κで切ったS\_\<κ値Hom-functorの存在と局所κ-small性の同じiffを直接与えない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity`

:::

:::definition "kerodon_8_3_3_7" (uses := "kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_4_4_5_3, kerodon_4_6_1_1")
Kerodon Notation 8.3.3.7（[Tag 03N4](https://kerodon.net/tag/03N4)）。対応表の状態：一部。

Cを宇宙で小さく取るとhomInfinityJointEvaluationは原文のHom(-,-)という同じ二変数の標準空間値関手を直接構成する。任意に選んだHの値とoriented fiber productの自然比較全体は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedArrowHomInfinity`、`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.homInfinityJointEvaluation`

:::

:::proposition "kerodon_8_3_3_8" (uses := "kerodon_1_4_0_1, kerodon_8_3_2_18")
Kerodon Proposition 8.3.3.8（[Tag 046C](https://kerodon.net/tag/046C)）。対応表の状態：なし。

二変数Homを各片側で制限した関手があるだけでは、原文の同じ指定頂点ηの普遍性と余普遍性が一致するbalanced条件を直接結論しない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafInfinity`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.covariantRepresentableInfinity`

:::

:::definition "kerodon_8_3_3_9" (uses := "kerodon_1_4_0_1, kerodon_8_3_3_1")
Kerodon Definition 8.3.3.9（[Tag 03NF](https://kerodon.net/tag/03NF)）。対応表の状態：一部。

小さいCではyonedaInfinityMapとcoyonedaInfinityMapは同じ標準Hom関手をcurryした共変・反変のYoneda関手を直接構成する。任意の指定hがYonedaであるという述語の全定義は含まない。

*定義 14.4 （Yoneda 埋め込み）*

小さい quasicategory $`C` について、$`\mathrm{Map}_C` と成分の入れ替え $`C\times C^{\mathrm{op}}\cong C^{\mathrm{op}}\times C` の合成 $`C\times C^{\mathrm{op}}\to\mathcal S` に、定理 2.4 の全単射で対応する射を

$$`j\colon C\to\mathcal P(C)`

と書き、Yoneda 埋め込みという。頂点 $`y` について $`j(y)=h_y`（定義 14.3）である。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coyonedaInfinityMap`

:::

:::definition "kerodon_8_3_3_12"
Kerodon Variant 8.3.3.12（[Tag 03V4](https://kerodon.net/tag/03V4)）。対応表の状態：なし。

SpaceInfinityの宇宙指定は原文の特定κで切ったS\_\<κではなく、局所κ-small性と二種のYoneda存在のiffへの比較もない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity`

:::

:::theorem "kerodon_8_3_3_13" (uses := "kerodon_1_4_0_1, kerodon_8_3_2_20, kerodon_8_3_3_8")
Kerodon Theorem 8.3.3.13（[Tag 03NJ](https://kerodon.net/tag/03NJ)）。対応表の状態：一部。

Cを宇宙で小さく標準Yonedaに指定すれば、yonedaInfinityMap\_isFullyFaithfulとcoyonedaInfinityMap\_isFullyFaithfulは原文の両方の充満忠実性を直接返す。本質的像の全特徴付けと任意に選んだYoneda関手は含まない。

*定理 15.2 （Yoneda の補題）*

- Yoneda 埋め込み $`j\colon C\to\mathcal P(C)`（定義 14.4）は充満忠実（定義 13.3）である。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap_isFullyFaithful`、`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coyonedaInfinityMap_isFullyFaithful`、`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coyonedaInfinityMap`

:::

:::proposition "kerodon_8_3_3_14" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1")
Kerodon Proposition 8.3.3.14（[Tag 03NP](https://kerodon.net/tag/03NP)）。対応表の状態：一部。

Cを宇宙で小さくhをyonedaInfinityMapとした場合、yonedaInfinityMap\_isLimitは同じ錐の極限性の保存を直接返す。反映もyonedaInfinityMapの充満忠実性と極限の写像空間判定から得る範囲で、任意のYonedaの選択へは広げない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.isLimitCone_iff_covariantRepresentableInfinity`、`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap_isLimit`

:::

:::definition "kerodon_8_3_3_15" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_7_1_8_2, kerodon_7_4_1_22")
Kerodon Variant 8.3.3.15（[Tag 03V5](https://kerodon.net/tag/03V5)）。対応表の状態：なし。

宇宙内のSpaceInfinity値の保存・検出は、原文の指定λで切ったS\_\<λとecf(λ)-小形状の同じiffへの比較を含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.isLimitCone_iff_covariantRepresentableInfinity`、`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap_isLimit`

:::

:::corollary "kerodon_8_3_3_17" (uses := "kerodon_1_4_0_1, kerodon_7_4_1_15, kerodon_7_4_3_8, kerodon_8_3_3_13")
Kerodon Corollary 8.3.3.17（[Tag 03Y7](https://kerodon.net/tag/03Y7)）。対応表の状態：一部。

Cを宇宙で小さく取るとyonedaInfinityMap\_isFullyFaithfulとyonedaInfinityMap\_isLimitは同じ前層圏への充満忠実なFの存在と小形状の極限保存を直接返す。任意の数値κについて標的がκ完備・κ余完備という大きさの比較は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap_isFullyFaithful`、`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafInfinity_hasLimit`、`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafInfinity_hasColimit`、`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap_isLimit`

:::

# 8.3.4 Representable Profunctors

%%%
number := false
tag := "kerodon-8-3-4"
%%%

Kerodon [Tag 03NQ](https://kerodon.net/tag/03NQ)

:::proposition "kerodon_8_3_4_1" (uses := "kerodon_1_4_0_1, kerodon_8_3_3_7, kerodon_8_3_3_13")
Kerodon Proposition 8.3.4.1（[Tag 03NR](https://kerodon.net/tag/03NR)）。対応表の状態：一部。

C,Dを宇宙で小さく標準Homに指定すると、Yonedaの充満忠実性をIsFullyFaithful.postcomposeへ渡しcurryすれば同じG↦Hom(-,G-)の充満忠実性を直接得る。本質的像が全表現可能profunctorで尽きる部分と指定κの大きさの比較は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap_isFullyFaithful`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful.postcompose`

:::

:::definition "kerodon_8_3_4_2" (uses := "kerodon_1_4_0_1, kerodon_8_3_3_2")
Kerodon Definition 8.3.4.2（[Tag 03NS](https://kerodon.net/tag/03NS)）。対応表の状態：なし。

対象ごとのHom(x,G-)の余表現可能性は原文の全二変数profunctor Kが同じHom(-,G-)にFunctorIsoで同型という条件ではない。その二変数の同型・選択不変性の型を引用に含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.exists_leftAdjoint_iff_covariantHom_representable`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.covariantRepresentableInfinity`

:::

:::definition "kerodon_8_3_4_4"
Kerodon Variant 8.3.4.4（[Tag 03NU](https://kerodon.net/tag/03NU)）。対応表の状態：なし。

各yのHom(-,y)の表現可能性と随伴の存在は、原文の同じKとHom(F-,-)との全二変数の同型を定義しない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.exists_leftAdjoint_iff_covariantHom_representable`、`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.exists_rightAdjoint_of_contravariantHom_representable`

:::

:::proposition "kerodon_8_3_4_9" (uses := "kerodon_1_4_0_1, kerodon_8_2_5_1")
Kerodon Proposition 8.3.4.9（[Tag 03PA](https://kerodon.net/tag/03PA)）。対応表の状態：一部。

Kを標準Hom(-,G-)とし小さい準圏を用いると、exists\_leftAdjoint\_iff\_covariantHom\_representableは原文末尾の「Kが各xで余表現可能⇔Gに左随伴が存在する」を直接返す。固定Fによる二変数のcorepresentationの全判定は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.exists_leftAdjoint_iff_covariantHom_representable`、`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.CouplingsOfInfinityCategories.adjunctionCovariantHomIso`

:::

:::corollary "kerodon_8_3_4_10" (uses := "kerodon_1_4_0_1, kerodon_8_3_4_1, kerodon_8_3_4_9")
Kerodon Corollary 8.3.4.10（[Tag 04B7](https://kerodon.net/tag/04B7)）。対応表の状態：一部。

両圏をpresentableに強めるとpresentableAdjointFunctorEquivalenceとそのadjunctionフィールドは原文(3)の同じ左右随伴関手の全準圏の反転同値と対応を直接返す。profunctorの部分圏Eを経る指定合成ρ⁻¹λとの同定は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.presentableAdjointFunctorEquivalence`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.presentableAdjointFunctorEquivalence_adjunction`

:::

:::definition "kerodon_8_3_4_11" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointSpaceVertex, SSet.const")
Kerodon Notation 8.3.4.11（[Tag 03MS](https://kerodon.net/tag/03MS)）。対応表の状態：本体にある。

pointSpaceVertexをSSet.constで任意E上の定値射にすれば、原文の同じΔ⁰を値とする定値関手全体を直接構成する。値圏の型だけという旧引用を補った。

:::

:::definition "kerodon_8_3_4_12" (uses := "kerodon_1_4_0_1, kerodon_5_6_6_2")
Kerodon Definition 8.3.4.12（[Tag 03NX](https://kerodon.net/tag/03NX)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Tw の始域固定の恒等頂点と個別前層の表現可能述語はある。任意の G と K について定値一点からの β を Tw(D) の各恒等射で評価し、指定された G(D) による表現を要求する述語は見つからない。

:::

:::proposition "kerodon_8_3_4_15" (uses := "kerodon_1_4_0_1, kerodon_8_2_4_3, kerodon_8_3_4_2, kerodon_8_3_4_12")
Kerodon Proposition 8.3.4.15（[Tag 03P5](https://kerodon.net/tag/03P5)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：充満忠実な関手による前層の制限比較と随伴の Hom 比較はある。G を固定した profunctor の表現可能性を Tw(D) 上で条件を満たす β の存在へ移す iff は見つからない。

:::

:::definition "kerodon_8_3_4_16" (uses := "kerodon_1_4_0_1, kerodon_5_6_6_1")
Kerodon Variant 8.3.4.16（[Tag 03P8](https://kerodon.net/tag/03P8)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Tw の両端交換の式と個別関手の余表現可能性はある。Tw(C) の各恒等射で β を評価して F(X) の余表現性を要求し、反対圏での表現条件と同定する型は見つからない。

:::

:::proposition "kerodon_8_3_4_19" (uses := "kerodon_1_4_0_1, kerodon_8_2_4_9, kerodon_8_3_4_12")
Kerodon Proposition 8.3.4.19（[Tag 03P2](https://kerodon.net/tag/03P2)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：任意の写像の左余終性の slice 判定と固定底の関手空間の引き戻し比較はある。β が誘導する Tw(D)→\{Δ⁰\}×⃗\_S(Cᵒᵖ×D) の左余終性を β の表現性と結ぶ型は見つからない。

:::

:::proposition "kerodon_8_3_4_20" (uses := "kerodon_1_4_0_1, kerodon_7_3_8_24, kerodon_7_4_2_13, kerodon_8_3_4_19")
Kerodon Proposition 8.3.4.20（[Tag 03P3](https://kerodon.net/tag/03P3)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：一般の左 Kan 延長述語と、別の Yoneda 重みの左 Kan 延長はある。表現を与える β により、Tw(D) の定値一点から Gᵒᵖ×id を介して K を左 Kan 延長する型は見つからない。

:::

:::corollary "kerodon_8_3_4_21"
Kerodon Corollary 8.3.4.21（[Tag 046K](https://kerodon.net/tag/046K)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：左 Kan 延長の一般の Hom 比較は h Fun の Hom 集合を扱い、固定底の相対関手空間の Kan 性もある。表現を与える β に対し、指定された二つの Kan 写像空間の間でホモトピー同値となる型は見つからない。

:::

# 8.3.5 Recognition of Hom-Functors

%%%
number := false
tag := "kerodon-8-3-5"
%%%

Kerodon [Tag 046H](https://kerodon.net/tag/046H)

:::definition "kerodon_8_3_5_1" (uses := "kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_8_1_1_11")
Kerodon Definition 8.3.5.1（[Tag 03MT](https://kerodon.net/tag/03MT)）。対応表の状態：一部。

Hとαを標準twistedArrowHomInfinityのpointed displayに指定すると、twistedArrowPointedDisplayFiberとその同値性は原文の同じ各(X,Y)のfiber比較を構成する。任意の指定H,αの述語全体は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowPointedDisplayFiber`、`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowPointedDisplayFiber_isQCatEquivalence`

:::

:::proposition "kerodon_8_3_5_5"
Kerodon Proposition 8.3.5.5（[Tag 03NK](https://kerodon.net/tag/03NK)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：標準 Hom の pointed 比較の各ファイバーでの同値と始域固定の恒等頂点の初期性はある。任意の α について、両端ファイバーでの同値を恒等関手による左右いずれかの表現性へ置き換える三条件は見つからない。

:::

:::proposition "kerodon_8_3_5_6" (uses := "kerodon_1_4_0_1, kerodon_7_3_6_5, kerodon_7_4_2_13, kerodon_8_3_3_2, kerodon_8_3_5_1")
Kerodon Proposition 8.3.5.6（[Tag 03N3](https://kerodon.net/tag/03N3)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：左 Kan 延長と h Fun の Hom 比較、および標準 Hom のファイバー比較はある。任意の H,α のファイバー条件を Tw 射影に沿う一点の左 Kan 延長および向き付き引き戻しの初期性と同定する型は見つからない。

:::

:::definition "kerodon_8_3_5_7"
Kerodon Variant 8.3.5.7（[Tag 03V3](https://kerodon.net/tag/03V3)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：一つの宇宙での標準 Tw 分類と、小空間の余極限を宇宙変更から反映する型はある。局所 κ-small の条件で指定 H と α の三つの同値を S\_\{\<κ\} へ制限する型は見つからない。

:::

:::corollary "kerodon_8_3_5_8"
Kerodon Corollary 8.3.5.8（[Tag 046J](https://kerodon.net/tag/046J)）。対応表の状態：なし。

引用は充満忠実Fに沿う標準Yonedaの関手同型。原文の任意に指定したα,βを保つ三角形のγと同一視する可換式がなく、同型があるだけは指定γの存在と数えない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.FullyFaithfulJointHom.yonedaInfinityMap_fullyFaithfulRestrictionIso`

:::

# 8.3.6 Strict Models for Hom-Functors

%%%
number := false
tag := "kerodon-8-3-6"
%%%

Kerodon [Tag 03N5](https://kerodon.net/tag/03N5)

:::definition "kerodon_8_3_6_1"
Kerodon Construction 8.3.6.1（[Tag 03N6](https://kerodon.net/tag/03N6)）。対応表の状態：一部。

representableHomCoherent xは原文の同じ豊穣Homを第一変数xで固定したcoherent実現を直接構成する。両変数が動く豊穣関手の全構成は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representableHomCoherent`

:::

:::proposition "kerodon_8_3_6_2"
Kerodon Proposition 8.3.6.2（[Tag 03N7](https://kerodon.net/tag/03N7)）。対応表の状態：一部。

representableHomCoherentIso xは各固定xで同じ豊穣Homの実現と標準Homの片変数のFunctorIsoを直接与える。全二変数でTw couplingを分類することへの比較は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representableHomCoherentIso`、`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.edgewiseEnrichedInfinityMap_isQCatEquivalence`

:::

:::definition "kerodon_8_3_6_5"
Kerodon Construction 8.3.6.5（[Tag 03NA](https://kerodon.net/tag/03NA)）。対応表の状態：なし。

標準left straighteningによるpointed displayは、原文のPathとI↦Ī∪Iから指定された豊穣Homのdisplayとは異なる構成。底H\_Cまで含めた同じ射への比較がない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowPointedDisplay`、`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowPointedDisplay_projection`

:::

:::proposition "kerodon_8_3_6_7"
Kerodon Proposition 8.3.6.7（[Tag 03ND](https://kerodon.net/tag/03ND)）。対応表の状態：なし。

標準Homのpointed displayのfiber同値性は、原文の豊穣Path構成の同じ(8.57)のcategorical pullback性を結論する型ではない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowPointedDisplayFiber_isQCatEquivalence`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityReconstruction_isPrecompositionEquivalence`

:::

# 8.3.7 Hom-Functors for Oriented Fiber Products

%%%
number := false
tag := "kerodon-8-3-7"
%%%

Kerodon [Tag 06BY](https://kerodon.net/tag/06BY)

:::theorem "kerodon_8_3_7_1" (uses := "kerodon_1_4_0_1, kerodon_4_5_3_28, kerodon_4_6_4_2, kerodon_8_1_1_6, kerodon_8_3_7_4, kerodon_8_3_7_6, kerodon_8_3_7_7")
Kerodon Theorem 8.3.7.1（[Tag 06BZ](https://kerodon.net/tag/06BZ)）。対応表の状態：一部。

laxPullbackMappingSpaceCone\_isLimitは各固定二頂点x,yで、原文の同じ四つのHom空間と成分による極限錐を直接返す。全(x,y)で自然に組み立てた関手準圏内の指定squareの存在までは含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxPullbackMappingSpaceCone_isLimit`

:::

:::definition "kerodon_8_3_7_3" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1")
Kerodon Notation 8.3.7.3（[Tag 06C2](https://kerodon.net/tag/06C2)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：元の lax pullback の固定二頂点の写像空間図式と Tw 射影の自然性はある。Tw(α) の三つの頂点を用いて E₋・E₊ と Q₋・Q₊ の指定の可換四角形を作る宣言は見つからない。

:::

:::lemma_ "kerodon_8_3_7_4" (uses := "kerodon_4_2_6_1, kerodon_8_1_1_11")
Kerodon Lemma 8.3.7.4（[Tag 06C3](https://kerodon.net/tag/06C3)）。対応表の状態：なし。

leftFibration\_pullback\_sndと分類図式のbaseChangeIsoは一般のpullbackについてで、原文のE\_±と指定U\_±がそのpullbackである同定を含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityDiagram_baseChangeIso`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibration_pullback_snd`

:::

:::proposition "kerodon_8_3_7_6" (uses := "kerodon_1_4_0_1, kerodon_4_5_3_19, kerodon_4_5_3_22, kerodon_4_5_3_24, kerodon_4_5_3_27, kerodon_4_5_3_33, kerodon_8_1_1_16, kerodon_8_1_2_17, kerodon_8_3_7_3, kerodon_8_3_7_4")
Kerodon Proposition 8.3.7.6（[Tag 06C6](https://kerodon.net/tag/06C6)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：固定二頂点の写像空間の極限と、一般の unstraightening の厳密な基底変換はある。Tw(C\_\{±\}) を左上とし E₋・E₊ を用いる指定正方形自体の categorical pullback 性は見つからない。

:::

:::lemma_ "kerodon_8_3_7_7" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_5_1_4_1, kerodon_5_3_3_1, kerodon_5_3_3_16, kerodon_5_3_3_18, kerodon_7_3_8_8")
Kerodon Lemma 8.3.7.7（[Tag 06C8](https://kerodon.net/tag/06C8)）。対応表の状態：一部。

四つの底D\_ijを同じ小準圏X、全底射を恒等、上面をleft fibrationsのstrict pullbackとした場合、leftFibrationPullbackClassifiedCone\_isLimitは同じ四分類図式の関手準圏内のpullbackを直接返す。可変底の一般のcubeは含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftFibrationPullbackClassifiedCone_isLimit`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityDiagram_baseChangeIso`

:::

