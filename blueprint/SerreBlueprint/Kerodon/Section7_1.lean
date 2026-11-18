import Verso
import VersoManual
import VersoBlueprint
import Mathlib.CategoryTheory.Limits.IsLimit
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.AdjunctionLimits
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CartesianInitialBoundary
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.Cocone
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ColimitDiagramIso
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoreLimit
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.EquivalenceAllLimits
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.EquivalenceColimitCones
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.FullyFaithfulConeReflection
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.FunctorLimits
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.FunctorPointwiseColimitExistence
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.FunctorPointwiseColimits
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.FunctorPointwiseLimitCriterion
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.FunctorPointwiseLimitExistence
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.LeftAdjointAllColimitPreservation
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.LimitDiagramIso
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeCoconeCriterion
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeCoconeRestriction
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeColimit
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeInitialBoundary
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeLimit
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.SquareFunctorTransport
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TerminalTransport
import SerrePositivity.KST.SConstruction.FunctorInitialVertices

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "7.1 Limits and Colimits" =>
%%%
number := false
tag := "kerodon-7-1"
%%%

Kerodon の 7.1 節（[Tag 02H1](https://kerodon.net/tag/02H1)）の項目と、SerrePositivity・Mathlib の宣言との対応。本文は対応表（research/kerodon-coverage）の判定の理由の要約で、Kerodon の本文の写しではない。

:::definition "kerodon_7_1_0_1" (lean := "CategoryTheory.Limits.IsLimit")
Kerodon Definition 7.1.0.1（[Tag 02H2](https://kerodon.net/tag/02H2)）。対応表の状態：Mathlib にある。

仮定：通常圏 K,C と F:K⥤C、頂点 Y を持つ錐（Kerodon と一致）。結論：IsLimit の lift・fac・uniq は、任意の X からの錐と Hom(X,Y) の対応が全単射であること（原文と一致）。

:::

# 7.1.1 Limits and Colimits in ∞-Categories

%%%
number := false
tag := "kerodon-7-1-1"
%%%

Kerodon [Tag 02VY](https://kerodon.net/tag/02VY)

:::definition "kerodon_7_1_1_1" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_6_8_15")
Kerodon Definition 7.1.1.1（[Tag 02VZ](https://kerodon.net/tag/02VZ)）。対応表の状態：なし。

引用はjoin錐のsliceの終対象性とright-fibration evaluation、余錐のcosliceの始対象性。原文の定値関手へのHomから指定自然変換との合成という同じ写像を比較する型がなく、別の評価の同値判定だけを定義の成分とはしない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isLimitCone_iff_mappingEvaluation_homotopyEquivalence`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isColimitCone_iff_coconePointHomFamily_homotopyEquivalence`

:::

:::definition "kerodon_7_1_1_12"
Kerodon Definition 7.1.1.12（[Tag 02JB](https://kerodon.net/tag/02JB)）。対応表の状態：なし。

HasLimit pは図式に対する極限錐の存在で、原文の指定したYを頂点とする自然変換の存在を直接述べない。join錐と指定自然変換の比較もこの型にはない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit`

:::

:::proposition "kerodon_7_1_1_13" (uses := "kerodon_1_4_0_1")
Kerodon Proposition 7.1.1.13（[Tag 02JH](https://kerodon.net/tag/02JH)）。対応表の状態：一部。

limitVertexIsoは原文のX,Yがともに同じuの極限ならX≅Yという極限側の向きを直接返す。任意の同型な頂点に極限錐を厳密に持ち上げる逆は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.limitVertexIso`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.limitConeIso`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.isLimitCone_iff_of_vertexIso`

:::

:::definition "kerodon_7_1_1_14"
Kerodon Notation 7.1.1.14（[Tag 02JJ](https://kerodon.net/tag/02JJ)）。対応表の状態：一部。

limitVertexIsoとcolimitVertexIsoは原文のlim/colimの同型類が図式だけで定まるという一意性を直接与える。任意の存在証明からの記法としての選択は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.limitVertexIso`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitVertexIso`

:::

:::definition "kerodon_7_1_1_15"
Kerodon Definition 7.1.1.15（[Tag 02JK](https://kerodon.net/tag/02JK)）。対応表の状態：一部。

HasLimitを全p:K→Cで量化すると原文のK-indexed limitsの条件を直接表す。名前付き述語の有無は理由とせず、colimits側は引用にないため数えない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit`、`SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallLimits`

:::

:::definition "kerodon_7_1_1_16"
Kerodon Variant 7.1.1.16（[Tag 0390](https://kerodon.net/tag/0390)）。対応表の状態：一部。

HasFiniteLimits・HasSmallLimits・HasSmallColimitsはそれぞれ原文の有限極限・小極限・小余極限の存在条件を直接表す。有限余極限と任意の形状族の全定義は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits`、`SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallLimits`、`SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits`

:::

:::definition "kerodon_7_1_1_18" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_6_2_1_19")
Kerodon Definition 7.1.1.18（[Tag 05Q9](https://kerodon.net/tag/05Q9)）。対応表の状態：一部。

constantFunctorMapは原文の同じ対角δの実際の射を直接構成する。任意Tの左右随伴によるlimit/colimit functorという二つの述語全体は引用のchosenColimitFunctorだけからは得ない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.chosenColimitFunctor`

:::

:::proposition "kerodon_7_1_1_19"
Kerodon Proposition 7.1.1.19（[Tag 02JL](https://kerodon.net/tag/02JL)）。対応表の状態：一部。

chosenColimitAdjunctionは全てのK図式の余極限が存在すれば同じ対角に左随伴が存在するという余極限側の方向を直接返す。極限側と逆は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.chosenColimitAdjunction`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneFamilyAdjunctHom_isIso`

:::

# 7.1.2 Constant Diagrams

%%%
number := false
tag := "kerodon-7-1-2"
%%%

Kerodon [Tag 03EX](https://kerodon.net/tag/03EX)

:::definition "kerodon_7_1_2_1" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_4_6_8_9")
Kerodon Definition 7.1.2.1（[Tag 03EY](https://kerodon.net/tag/03EY)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：∞圏の join 錐の極限性はある。豊穣圏の cotensor や presentable 圏の tensor とは別に、任意の∞圏で指定 e:K→Hom(X,Y) から作る普遍性の述語は見つからない。

:::

:::definition "kerodon_7_1_2_5"
Kerodon Notation 7.1.2.5（[Tag 03F2](https://kerodon.net/tag/03F2)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：錐の頂点同型は同一の図式に対する極限性から得る。指定 e が冪を与えるときの X の一意性や Yᴷ の構成は見つからない。

:::

:::proposition "kerodon_7_1_2_8" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_4_6_7_5, kerodon_4_6_8_9, kerodon_4_6_8_19")
Kerodon Proposition 7.1.2.8（[Tag 03F6](https://kerodon.net/tag/03F6)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：豊穣写像空間と coherent nerve の比較候補を探した。与えた e が豊穣冪を表すことと nerve 側で冪を表すことの iff は見つからない。

:::

:::definition "kerodon_7_1_2_11" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1")
Kerodon Variant 7.1.2.11（[Tag 05QA](https://kerodon.net/tag/05QA)）。対応表の状態：なし。

presentable圏のtensorSpaceFunctorは、原文の指定κの空間部分圏でeが点のcopowerを表すことと弱ホモトピー同値のiffではない。対象・射・濃度が異なる。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.tensorSpaceFunctor`

:::

:::proposition "kerodon_7_1_2_15"
Kerodon Proposition 7.1.2.15（[Tag 048B](https://kerodon.net/tag/048B)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：一般の極限性の述語はある。大きい添字集合による自己冪の存在を、順序集合の nerve と同値であることと比較する型は見つからない。

:::

:::proposition "kerodon_7_1_2_16"
Kerodon Proposition 7.1.2.16（[Tag 03FB](https://kerodon.net/tag/03FB)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：極限錐と DG nerve の写像空間の型を探索した。正規化鎖からの f が冪を表す条件を DG 側と nerve 側で比較する型は見つからない。

:::

:::definition "kerodon_7_1_2_18"
Kerodon Variant 7.1.2.18（[Tag 03FD](https://kerodon.net/tag/03FD)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏で単体的対象の正規化複体はある。係数 A の正規化余鎖を DG nerve 内の指定された余積・極限として特徴付ける型は見つからない。

:::

# 7.1.3 Limit and Colimit Diagrams

%%%
number := false
tag := "kerodon-7-1-3"
%%%

Kerodon [Tag 02JA](https://kerodon.net/tag/02JA)

:::proposition "kerodon_7_1_3_1" (uses := "kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_5_2_8_6, kerodon_5_2_8_7, kerodon_5_6_6_21")
Kerodon Proposition 7.1.3.1（[Tag 02W7](https://kerodon.net/tag/02W7)）。対応表の状態：なし。

sliceの終対象とその評価の同値判定だけでは、原文の定値対角とuによる指定oriented fiber productの対象αに直接移せない。laxSlice/錐の族の比較はあるが、この指定fiber productとの同定を引用型に含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isLimitCone_iff_mappingEvaluation_homotopyEquivalence`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone`

:::

:::corollary "kerodon_7_1_3_2"
Kerodon Corollary 7.1.3.2（[Tag 02W8](https://kerodon.net/tag/02W8)）。対応表の状態：なし。

引用は全ての共変表現可能関手で極限を検出するiff。原文の一つのYが指定right fibrationを表現するという(2),(3)への比較を直接与えない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.isLimitCone_iff_covariantRepresentableInfinity`

:::

:::corollary "kerodon_7_1_3_3"
Kerodon Corollary 7.1.3.3（[Tag 02W9](https://kerodon.net/tag/02W9)）。対応表の状態：一部。

HasLimitとIsLimitConeを展開すると同じslice C\_/uに終対象が存在するという原文(1)⇔(3)。oriented fiber productの条件(2)は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit`

:::

:::definition "kerodon_7_1_3_4" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone")
Kerodon Definition 7.1.3.4（[Tag 02JM](https://kerodon.net/tag/02JM)）。対応表の状態：本体にある。

仮定：K 上の p と左 join からの延長 c。述語の形成自体は Quasicategory C を要求しない（Lean が弱い）。結論：IsLimitCone c は sliceOver p の頂点 c が IsTerminalVertex（原文と一致）。

:::

:::definition "kerodon_7_1_3_5" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone")
Kerodon Variant 7.1.3.5（[Tag 02JN](https://kerodon.net/tag/02JN)）。対応表の状態：本体にある。

仮定：K 上の p と右 join からの延長 d。述語の形成自体は Quasicategory C を要求しない（Lean が弱い）。結論：IsColimitCone d は sliceUnder p の頂点 d が IsInitialVertex（原文と一致）。

:::

:::proposition "kerodon_7_1_3_15"
Kerodon Proposition 7.1.3.15（[Tag 06TF](https://kerodon.net/tag/06TF)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：任意の join 錐の極限性は定義される。終頂点の指示写像 Q で指定された立方体の制限を比較する極限判定は見つからない。

:::

:::proposition "kerodon_7_1_3_17" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_4_3_6_12, kerodon_4_4_1_11, kerodon_4_5_6_20, kerodon_4_7_3_12, kerodon_5_1_6_4, kerodon_7_1_3_4")
Kerodon Proposition 7.1.3.17（[Tag 02JU](https://kerodon.net/tag/02JU)）。対応表の状態：一部。

coneIteratedSliceIso\_restrictionはC\_/cからC\_/pへの同じ制限射を(sliceOver p)\_/cの射影に同型で対応させる。isLimitCone\_iff\_trivialKanFibrationをこの同じ射に移せば原文(1)⇔(2)を直接得る。(3),(4)からの逆は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isLimitCone_iff_trivialKanFibration`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coneIteratedSliceIso_restriction`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coneIteratedSliceIso`

:::

:::proposition "kerodon_7_1_3_18" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_4_4_4")
Kerodon Proposition 7.1.3.18（[Tag 0391](https://kerodon.net/tag/0391)）。対応表の状態：一部。

ρを全錐図式のFunctorIsoと強めるとIsLimitCone.of\_functorIsoは同じ全図式の極限性を移し、原文(1)⇒(2)を直接与える。K上の各成分だけの可逆性からの全二取三は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone.of_functorIso`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone.of_functorIso`

:::

:::corollary "kerodon_7_1_3_19" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.isLimitCone_iff_of_vertexIso, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isLimitCone_iff_of_diagram_eq, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone.of_functorIso, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone.of_functorIso") (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1")
Kerodon Corollary 7.1.3.19（[Tag 02K1](https://kerodon.net/tag/02K1)）。対応表の状態：本体にある。

現本体SquareFunctorTransportのIsLimitCone.of\_functorIsoとIsColimitCone.of\_functorIsoは全錐／全余錐のFunctorIsoで極限性／余極限性を保つ。逆は同じ同型のsymmに適用するだけで、原文の二つのiff全体を直接得る。slice内の同型だけという従来の理由を訂正。

:::

:::corollary "kerodon_7_1_3_20" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.hasLimit_iff_of_functorIso, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.hasColimit_iff_of_functorIso")
Kerodon Corollary 7.1.3.20（[Tag 02K2](https://kerodon.net/tag/02K2)）。対応表の状態：本体にある。

仮定：Quasicategory C、K 上の p,q と FunctorIso p q（Kerodon と一致）。結論：HasLimit p↔HasLimit q と HasColimit p↔HasColimit q の両方（原文と一致）。

:::

# 7.1.4 Preservation of Limits and Colimits

%%%
number := false
tag := "kerodon-7-1-4"
%%%

Kerodon [Tag 02JV](https://kerodon.net/tag/02JV)

:::definition "kerodon_7_1_4_1"
Kerodon Definition 7.1.4.1（[Tag 0392](https://kerodon.net/tag/0392)）。対応表の状態：一部。

mapJoinCone F cの極限性は原文前半の同じlimit diagramをFに後合成した極限性そのもの。専用のpreservedという述語名がないことは不足とせず、colimit側の構成は引用に含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone`

:::

:::definition "kerodon_7_1_4_4"
Kerodon Definition 7.1.4.4（[Tag 02JW](https://kerodon.net/tag/02JW)）。対応表の状態：一部。

PreservesSmallLimits/Colimitsを固定した小形状Kに評価すると、同じ図式・錐の後合成を保存する原文条件を直接得る。任意の大きさのKについての全定義ではない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PreservesSmallLimits`、`SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits`

:::

:::definition "kerodon_7_1_4_5"
Kerodon Variant 7.1.4.5（[Tag 0395](https://kerodon.net/tag/0395)）。対応表の状態：一部。

PreservesSmallLimitsは原文の小極限保存の定義を直接表す。PreservesFiniteCoproductsは有限余積のみで有限余極限全体とはしない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PreservesSmallLimits`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.PreservesFiniteCoproducts`

:::

:::proposition "kerodon_7_1_4_12" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsQCatEquivalence.isLimitCone_iff, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.QCatEquivalence.isLimitCone_iff, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.equivalence_isColimitCone_iff")
Kerodon Proposition 7.1.4.12（[Tag 02JZ](https://kerodon.net/tag/02JZ)）。対応表の状態：本体にある。

仮定：二つの quasicategory、F の IsQCatEquivalence と任意の K 上の錐・余錐（Kerodon と一致）。結論：各錐の極限性と F で写した錐の極限性の iff、余錐の双対の iff（原文と一致）。

:::

:::definition "kerodon_7_1_4_13" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isLimitCone_of_fullyFaithful_image")
Kerodon Variant 7.1.4.13（[Tag 02WD](https://kerodon.net/tag/02WD)）。対応表の状態：本体にある。

仮定：二つの quasicategory、F の IsFullyFaithful と像の錐の IsLimitCone（Kerodon と一致）。結論：元の指定された錐の IsLimitCone（原文と一致）。

:::

:::definition "kerodon_7_1_4_14"
Kerodon Variant 7.1.4.14（[Tag 06TG](https://kerodon.net/tag/06TG)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：一般の極限性と右ファイブレーションの別々の述語はある。n-truncated なファイバーと (n+1)-connective な添字を同時に課す保存反映の iff は見つからない。

:::

:::corollary "kerodon_7_1_4_15"
Kerodon Corollary 7.1.4.15（[Tag 05YC](https://kerodon.net/tag/05YC)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：頂点上のスライスの射影で余極限性を比較する双対側はある。対象 X の n-truncated 性と添字の connectivity を使う極限版は見つからない。

:::

:::corollary "kerodon_7_1_4_17"
Kerodon Corollary 7.1.4.17（[Tag 05YE](https://kerodon.net/tag/05YE)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏のスライス引き戻し関手は向きが逆。原文の f₊ による n-truncated 射上の極限性の iff は見つからない。

:::

:::corollary "kerodon_7_1_4_18"
Kerodon Corollary 7.1.4.18（[Tag 02K3](https://kerodon.net/tag/02K3)）。対応表の状態：一部。

与えられた極限錐cの存在証人にIsQCatEquivalence.isLimitCone\_iffの順方向を適用し、原文(1)の存在の順方向を直接得る。添字前合成の存在iffは終域同値の逆方向の代用にしない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsQCatEquivalence.isLimitCone_iff`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.hasLimit_iff_restrict_of_precompositionEquivalence`

:::

:::corollary "kerodon_7_1_4_19"
Kerodon Corollary 7.1.4.19（[Tag 02K4](https://kerodon.net/tag/02K4)）。対応表の状態：一部。

C,Dの一方が全小極限／全小余極限を持つと強めればHasSmallLimits.of\_equivalenceとHasSmallColimits.of\_equivalenceは、同じ小形状Kについて他方の存在を直接与える。逆はe.symm。Kだけの存在からの一般の比較は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.HasSmallLimits.of_equivalence`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.HasSmallColimits.of_equivalence`

:::

:::proposition "kerodon_7_1_4_21"
Kerodon Proposition 7.1.4.21（[Tag 02K6](https://kerodon.net/tag/02K6)）。対応表の状態：一部。

原文のK-indexed limitsの存在から証人dを取り、保存性でhFdを得ればisLimitCone\_of\_conservative\_imageは同じcの像から極限性を反映する。順方向は入力の保存性であり、極限側のiff全体が直接従う。余極限側は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isLimitCone_of_conservative_image`

:::

:::lemma_ "kerodon_7_1_4_22" (uses := "kerodon_1_4_0_1, kerodon_4_4_2_12")
Kerodon Lemma 7.1.4.22（[Tag 02K7](https://kerodon.net/tag/02K7)）。対応表の状態：一部。

isLimitCone\_of\_conservative\_imageは原文と同じ保存された証人dと保守性の下で、F(c)が極限ならcが極限となる方向を直接返す。逆をこの引用型だけには含めない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isLimitCone_of_conservative_image`

:::

:::definition "kerodon_7_1_4_23"
Kerodon Definition 7.1.4.23（[Tag 02K8](https://kerodon.net/tag/02K8)）。対応表の状態：なし。

MathlibのCreatesLimit/CreatesColimitは通常圏の錐とその同型による持ち上げ。原文の任意単体形状Kのjoin錐と同じ保存された極限図式へのnerve比較がない。

宣言：`CategoryTheory.CreatesLimit`、`CategoryTheory.CreatesColimit`

:::

:::proposition "kerodon_7_1_4_25" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1")
Kerodon Proposition 7.1.4.25（[Tag 02KA](https://kerodon.net/tag/02KA)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の CreatesLimit はある。原文の K 上の極限存在と保存の連言との iff は∞圏の型では見つからない。

:::

:::proposition "kerodon_7_1_4_26" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_7_3_19, kerodon_7_1_3_17")
Kerodon Proposition 7.1.4.26（[Tag 02KB](https://kerodon.net/tag/02KB)）。対応表の状態：一部。

A=Δ⁰、fが頂点の場合、sliceOver\_hasColimit\_of\_projectionで余極限錐を取り、sliceOver\_isColimitCone\_iff\_projectionで同じ錐の像の余極限性を直接得る。原文(2)のこの場合のみで、一般Aと(1)は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceOver_isColimitCone_iff_projection`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceOver_hasColimit_of_projection`

:::

:::corollary "kerodon_7_1_4_27" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_7_1_4_25, kerodon_7_1_4_26")
Kerodon Corollary 7.1.4.27（[Tag 02KC](https://kerodon.net/tag/02KC)）。対応表の状態：一部。

A=Δ⁰かつCが全小余極限を持つ場合、sliceOver\_hasSmallColimitsは同じsliceの各小Kの余極限存在を直接返す。一般Aでのcosliceの錐の持ち上げは極限性まで述べず、両側のiff全体は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceOver_hasSmallColimits`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.exists_cosliceCone_lift_of_isLimit`

:::

:::corollary "kerodon_7_1_4_28" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.mapJoinCone_isLimit_of_adjunction, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.mapJoinCocone_isColimit_of_adjunction")
Kerodon Corollary 7.1.4.28（[Tag 02KE](https://kerodon.net/tag/02KE)）。対応表の状態：本体にある。

仮定：二つの quasicategory と QCatAdjunction F G、任意の K（Kerodon と一致）。結論：G が極限錐を極限錐に、F が余極限錐を余極限錐に送る（原文と一致）。

:::

:::corollary "kerodon_7_1_4_29"
Kerodon Corollary 7.1.4.29（[Tag 04JW](https://kerodon.net/tag/04JW)）。対応表の状態：一部。

Cが全小余極限を持つと強めればreflectiveSubcategory\_hasSmallColimitsは同じ反射的full subcategoryで指定の小図式uの余極限存在を直接与える。一図式だけの周囲での存在からの一般化は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.hasSmallColimits_of_reflection`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.reflectiveSubcategory_hasSmallColimits`

:::

:::corollary "kerodon_7_1_4_31"
Kerodon Corollary 7.1.4.31（[Tag 06YB](https://kerodon.net/tag/06YB)）。対応表の状態：一部。

周囲のCが全小余極限を持つと強めると、reflectiveSubcategory\_hasSmallColimitsは同じ反射的部分圏について指定小Kの全図式の余極限存在を直接返す。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.reflectiveSubcategory_hasSmallColimits`

:::

:::definition "kerodon_7_1_4_33"
Kerodon Variant 7.1.4.33（[Tag 04JX](https://kerodon.net/tag/04JX)）。対応表の状態：一部。

reflective\_isLimitCone\_iff\_inclusionは原文の既存極限錐の包含による保存・反映を直接与える。さらにPの同型閉性を加えるとmem\_limitConeとfullSubcomplex\_hasLimit\_of\_apexで同じ図式の存在も移る。任意Pの存在反映は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.reflective_isLimitCone_iff_inclusion`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.reflective_mem_limitCone`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.fullSubcomplex_hasLimit_of_apex`

:::

:::lemma_ "kerodon_7_1_4_34"
Kerodon Lemma 7.1.4.34（[Tag 04JY](https://kerodon.net/tag/04JY)）。対応表の状態：一部。

部分圏をrepleteにも強めるとreflective\_mem\_limitConeの空添字の場合は同じ終頂点Xが部分圏に属すると直接返す。原文最後のrepleteの場合の結論に一致し、任意のreflective部分圏は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.reflective_mem_limitCone`

:::

:::corollary "kerodon_7_1_4_35"
Kerodon Corollary 7.1.4.35（[Tag 03Y1](https://kerodon.net/tag/03Y1)）。対応表の状態：一部。

周囲の全小極限／余極限の存在を加え、極限側はPの同型閉性も加えると、二つのreflectiveSubcategory\_hasSmall\*は同じ部分圏の指定小Kでの存在を直接返す。Kだけの存在の一般形ではない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.reflectiveSubcategory_hasSmallLimits`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.reflectiveSubcategory_hasSmallColimits`

:::

# 7.1.5 Relative Initial and Final Objects

%%%
number := false
tag := "kerodon-7-1-5"
%%%

Kerodon [Tag 02WE](https://kerodon.net/tag/02WE)

:::definition "kerodon_7_1_5_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.KanRelativeInitialVertex, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.KanRelativeTerminalVertex")
Kerodon Definition 7.1.5.1（[Tag 02KU](https://kerodon.net/tag/02KU)）。対応表の状態：本体にある。

仮定：写像 U:C→D と C の頂点。定義型には両方の Quasicategory を明示しない（Lean が弱い）。結論：相対終・始頂点はそれぞれ y への、y からの各 pinched Hom の比較が同値となる条件（原文と一致）。

:::

:::proposition "kerodon_7_1_5_10" (uses := "kerodon_1_4_0_1, kerodon_4_6_8_15")
Kerodon Proposition 7.1.5.10（[Tag 02WN](https://kerodon.net/tag/02WN)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：相対始性は retract に沿って移る。像の同型を仮定した指定辺で、二頂点の相対始性と辺の可逆性の三条件を比較する型は見つからない。

:::

:::corollary "kerodon_7_1_5_11"
Kerodon Corollary 7.1.5.11（[Tag 02WP](https://kerodon.net/tag/02WP)）。対応表の状態：一部。

Uをinner fibrationに強め、相対始／終性をInitial/TerminalBoundaryLiftingで持つ場合、of\_vertexIsoと同じeのsymmを使えば指定頂点X,Yの両方向の移送を直接得る。任意のUの写像空間による相対性への比較は含まない。

宣言：`SerrePositivity.InfinityCategories.HTT.InitialAndFinalObjects.InitialBoundaryLifting.of_vertexIso`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalBoundaryLifting.of_vertexIso`

:::

:::corollary "kerodon_7_1_5_12" (uses := "kerodon_1_4_0_1, kerodon_7_1_5_10")
Kerodon Corollary 7.1.5.12（[Tag 02WQ](https://kerodon.net/tag/02WQ)）。対応表の状態：一部。

Uをinner fibration、相対始性をInitialBoundaryLiftingに強めると、relativeInitialVertexIsoは原文のU(X)≅U(Y)からX≅Yを同じ二頂点について直接返す。逆は頂点同型のmap。一般Uへの比較は含まない。

宣言：`SerrePositivity.KST.SConstruction.relativeInitialVertexIso`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeInitialVertexIso`

:::

:::proposition "kerodon_7_1_5_13"
Kerodon Proposition 7.1.5.13（[Tag 0397](https://kerodon.net/tag/0397)）。対応表の状態：なし。

adjunctionOfRelativeInitialSectionは厳密sectionと境界充填から随伴を構成するが、原文のcoreflective localizationに要る左随伴の充満忠実性を結論しない。随伴だけは同じ結論の十分条件にならない。

宣言：`SerrePositivity.KST.LocalizingInvariants.adjunctionOfRelativeInitialSection`、`SerrePositivity.KST.LocalizingInvariants.adjunctionOfRelativeTerminalSection`

:::

:::lemma_ "kerodon_7_1_5_14"
Kerodon Lemma 7.1.5.14（[Tag 0398](https://kerodon.net/tag/0398)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：相対始頂点の述語はある。その全頂点が張る部分圏への制限が同値で、任意の射の coreflection 性を特徴付ける型は見つからない。

:::

:::corollary "kerodon_7_1_5_15"
Kerodon Corollary 7.1.5.15（[Tag 0399](https://kerodon.net/tag/0399)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：全空間の相対始性からファイバーの始性を得る。各ファイバーに相対始対象があることによる coreflective localization の iff は見つからない。

:::

:::proposition "kerodon_7_1_5_16" (uses := "kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_4_3_6_1, kerodon_4_6_5_10, kerodon_5_1_7_16")
Kerodon Proposition 7.1.5.16（[Tag 02WR](https://kerodon.net/tag/02WR)）。対応表の状態：一部。

Uをinner fibrationに強めると相対始性をInitialBoundaryLiftingへ移せ、relativeCosliceMap\_trivialKanFibration\_of\_initialBoundaryLiftingは原文(1)の同じ相対coslice比較を自明Kan、従って圏同値と直接返す。逆と相対終側は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeCosliceMap_trivialKanFibration_of_initialBoundaryLifting`

:::

:::corollary "kerodon_7_1_5_17" (uses := "kerodon_1_4_0_1, kerodon_4_3_6_9, kerodon_4_5_6_20, kerodon_7_1_5_16")
Kerodon Corollary 7.1.5.17（[Tag 02WS](https://kerodon.net/tag/02WS)）。対応表の状態：一部。

kanRelativeInitialVertex\_iff\_initialBoundaryは原文(1)⇔(3)、相対cosliceの補題は(3)⇒(2)を同じU,Yで直接返す。三条件の全同値は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanRelativeInitialVertex_iff_initialBoundary`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeCosliceMap_trivialKanFibration_of_initialBoundaryLifting`

:::

:::corollary "kerodon_7_1_5_18" (uses := "kerodon_1_4_0_1, kerodon_7_1_5_17")
Kerodon Corollary 7.1.5.18（[Tag 02WT](https://kerodon.net/tag/02WT)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：自明 Kan ファイブレーションは一頂点からの coslice 比較に対するもの。相対始頂点の充満部分圏の制限とは異なる。

:::

:::proposition "kerodon_7_1_5_19" (uses := "kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_3_3_7_5, kerodon_4_6_1_22, kerodon_5_1_1_1, kerodon_5_1_3_11, kerodon_5_1_4_1")
Kerodon Proposition 7.1.5.19（[Tag 02WU](https://kerodon.net/tag/02WU)）。対応表の状態：一部。

Fもinner fibrationと強めれば、相対始性と境界充填のiffをFとfiberのF\_Eに適用できる。total→fiberとcartesian辺保存下のfiber→totalの二型が原文の同じ頂点の結論を返す。任意Fには及ばない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialBoundaryLifting_fiber_of_total`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanInitialBoundaryLifting_of_fiber_map`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isTerminalVertex_fiber_iff_terminalBoundaryLifting`

:::

:::corollary "kerodon_7_1_5_21" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting.isInitialVertex_fiber, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialBoundaryLifting_of_isInitialVertex_fiber")
Kerodon Corollary 7.1.5.21（[Tag 02WV](https://kerodon.net/tag/02WV)）。対応表の状態：本体にある。

仮定：U のファイバーの頂点 x、順方向は相対始性の境界充填、逆方向は CartesianFibration U。原文の inner fibration 上で相対始性と境界充填を比較できる（Kerodon と一致）。結論：ファイバーの始頂点性と全空間での相対始性の二方向（原文と一致）。

:::

:::corollary "kerodon_7_1_5_22"
Kerodon Corollary 7.1.5.22（[Tag 039A](https://kerodon.net/tag/039A)）。対応表の状態：なし。

fiberの始対象から境界充填、厳密sectionから随伴を作る型だけでは原文(2)の左随伴の充満忠実性と一般のfiber条件からのsectionの選択を直接返さない。証明の部品のみ。

宣言：`SerrePositivity.KST.LocalizingInvariants.adjunctionOfRelativeInitialSection`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialBoundaryLifting_of_isInitialVertex_fiber`

:::

# 7.1.6 Relative Limits and Colimits

%%%
number := false
tag := "kerodon-7-1-6"
%%%

Kerodon [Tag 02KF](https://kerodon.net/tag/02KF)

:::definition "kerodon_7_1_6_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsRelativeColimitCone, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsRelativeLimitCone")
Kerodon Definition 7.1.6.1（[Tag 02KG](https://kerodon.net/tag/02KG)）。対応表の状態：本体にある。

仮定：写像 U:C→D、K 上の図式と join 錐または余錐（Kerodon と一致）。結論：IsRelativeLimitCone と IsRelativeColimitCone は、誘導された slice・coslice 上の相対終・始頂点性（原文と一致）。

:::

:::proposition "kerodon_7_1_6_9" (uses := "kerodon_1_4_0_1, kerodon_4_4_5_10, kerodon_4_5_4_11, kerodon_7_1_3_19")
Kerodon Proposition 7.1.6.9（[Tag 02X4](https://kerodon.net/tag/02X4)）。対応表の状態：なし。

引用は相対余極限余錐のFunctorIsoでの不変性。原文は相対極限錐であり、relative limit/reverseCoconeの比較はあるが、指定した全錐のFunctorIsoを反転余錐へ移す型を引用に含まない。双対の類似だけでは数えない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanIsRelativeColimitCone_iff_of_functorIso`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanIsRelativeColimitCone_congr`

:::

:::proposition "kerodon_7_1_6_10" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1")
Kerodon Proposition 7.1.6.10（[Tag 02KQ](https://kerodon.net/tag/02KQ)）。対応表の状態：なし。

引用はU,V自身の相対始頂点の合成と取消し。原文は図式のslice/coslice後合成に関する相対極限／余極限であり、その合成射・写った錐との比較を欠く。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.KanRelativeInitialVertex.comp`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.KanRelativeInitialVertex.cancel_right`

:::

:::corollary "kerodon_7_1_6_11" (uses := "kerodon_1_4_0_1, kerodon_7_1_6_10")
Kerodon Corollary 7.1.6.11（[Tag 02X5](https://kerodon.net/tag/02X5)）。対応表の状態：一部。

Vをtrivial Kan fibrationに強めればkanIsRelativeColimitCone\_comp\_iff\_of\_trivialKanFibrationは原文(2)の同じ余錐についてのiffを直接返す。一般の充満忠実Vと極限側は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanRelativeInitialVertex_comp_iff_of_fullyFaithful`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanIsRelativeColimitCone_comp_iff_of_trivialKanFibration`

:::

:::corollary "kerodon_7_1_6_12" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_7_1_6_10")
Kerodon Corollary 7.1.6.12（[Tag 02KR](https://kerodon.net/tag/02KR)）。対応表の状態：一部。

Uをinner fibrationに強め、相対余極限からKanRelativeCoconeLiftingへのiffを使えば、kanIsColimitCone\_of\_relativeLifting\_of\_imageは原文(2)の相対余極限と像の余極限から元の余極限を直接返す。極限側と逆は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanIsColimitCone_of_relativeLifting_of_image`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanIsRelativeColimitCone_iff_isColimit_of_terminal`

:::

:::proposition "kerodon_7_1_6_13" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_6_6_8, kerodon_5_1_1_1, kerodon_5_1_4_1, kerodon_5_3_7_5, kerodon_7_1_5_19")
Kerodon Proposition 7.1.6.13（[Tag 02XB](https://kerodon.net/tag/02XB)）。対応表の状態：なし。

引用は余錐族の相対始性と相対余極限。原文は錐の関手圏の指定相対制限への相対終性であり、同じ射・対象ではない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanRelativeCoconeLifting_iff_isRelativeColimitCone`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanIsRelativeColimitCone_iff_family_relativeInitial`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.KanRelativeCoconeLifting`

:::

:::corollary "kerodon_7_1_6_14"
Kerodon Corollary 7.1.6.14（[Tag 06MC](https://kerodon.net/tag/06MC)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：相対極限錐の述語はある。指定した底上の関手空間の制限のファイバーで終対象となる iff は見つからない。

:::

:::corollary "kerodon_7_1_6_15"
Kerodon Corollary 7.1.6.15（[Tag 06MD](https://kerodon.net/tag/06MD)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：底上の関手空間は構成される。指定された制限ファイバーの可縮性による U-極限性の iff は見つからない。

:::

:::corollary "kerodon_7_1_6_16" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isLimitCone_iff_terminalBoundaryLifting_coneRestriction, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isColimitCone_of_initialBoundaryLifting_coconeRestriction")
Kerodon Corollary 7.1.6.16（[Tag 02XD](https://kerodon.net/tag/02XD)）。対応表の状態：本体にある。

仮定：Quasicategory C と K 上の錐 c。制限 U は inner fibration として境界充填で相対終性を判定する（Kerodon と一致）。結論：IsLimitCone c と coneRestriction K C 上の c の TerminalBoundaryLifting が同値（原文の相対終性と一致）。

:::

:::corollary "kerodon_7_1_6_17" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_7_1_5_18, kerodon_7_1_6_16")
Kerodon Corollary 7.1.6.17（[Tag 05QH](https://kerodon.net/tag/05QH)）。対応表の状態：なし。

引用は相対joinのfiberごとの余極限図式からの制限。原文の全極限錐のfull subcategoryからFun(K,C)への制限と違う対象・射。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanRelativeJoinColimitRestriction_trivialKanFibration`

:::

:::proposition "kerodon_7_1_6_19" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_3_4_1_13, kerodon_4_3_6_12, kerodon_4_4_3_8, kerodon_4_6_5_10, kerodon_5_1_6_4, kerodon_7_1_6_1, kerodon_7_1_6_13")
Kerodon Proposition 7.1.6.19（[Tag 02X1](https://kerodon.net/tag/02X1)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：余錐族の相対始性を使う双対の判定はある。任意の錐と定値錐からの Hom の四角形のホモトピー引き戻し性との三条件の iff は見つからない。

:::

:::corollary "kerodon_7_1_6_20" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_7_1_6_19")
Kerodon Corollary 7.1.6.20（[Tag 05QE](https://kerodon.net/tag/05QE)）。対応表の状態：なし。

初期境界充填からのpinchedHomMap同値は始点固定の射、原文は終点に極限図式を固定する制限作用。terminalBoundaryの極限判定だけではその同じ全Hom制限の同値まで直接結論しない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.pinchedHomMap_equivalence_of_initialBoundary`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isLimitCone_iff_terminalBoundaryLifting_coneRestriction`

:::

# 7.1.7 Colimits Relative to a Fibration

%%%
number := false
tag := "kerodon-7-1-7"
%%%

Kerodon [Tag 069P](https://kerodon.net/tag/069P)

:::proposition "kerodon_7_1_7_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanRelativeCoconeLifting_iff_isRelativeColimitCone, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanRelativeCocone_lift_iff")
Kerodon Proposition 7.1.7.1（[Tag 069Q](https://kerodon.net/tag/069Q)）。対応表の状態：本体にある。

仮定：両端が quasicategory、U が InnerFibration、右 join 上の余錐（Kerodon と一致）。結論：IsRelativeColimitCone と KanRelativeCoconeLifting の iff。後者は K⋆∂Δⁿ から K⋆Δⁿ への始頂点を固定した持ち上げ（原文と一致）。

:::

:::corollary "kerodon_7_1_7_4" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_7_1_6_12")
Kerodon Corollary 7.1.7.4（[Tag 02KS](https://kerodon.net/tag/02KS)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の極限創出はある。弱可縮な K に対し左ファイブレーションで余極限、右ファイブレーションで極限を創出する型は見つからない。

:::

:::corollary "kerodon_7_1_7_5" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_7_1_4_25, kerodon_7_1_7_4")
Kerodon Corollary 7.1.7.5（[Tag 02KT](https://kerodon.net/tag/02KT)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：一図式の余極限存在は定義される。弱可縮な K の底の存在から全空間の存在と射影の保存を同時に得る型は見つからない。

:::

:::proposition "kerodon_7_1_7_6" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_7_1_7_1")
Kerodon Proposition 7.1.7.6（[Tag 069R](https://kerodon.net/tag/069R)）。対応表の状態：なし。

KanRelativeInitialVertex.pullback\_sndは対象の相対始性の底変換。原文は相対余極限図式で、図式のcoslice後合成の底変換との同定を引用に含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.KanRelativeInitialVertex.pullback_snd`

:::

:::corollary "kerodon_7_1_7_7"
Kerodon Corollary 7.1.7.7（[Tag 069S](https://kerodon.net/tag/069S)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：相対始頂点の厳密引き戻しの型はある。任意の categorical pullback で指定 K▷ 図式の相対余極限性を反映する型は見つからない。

:::

:::corollary "kerodon_7_1_7_8"
Kerodon Corollary 7.1.7.8（[Tag 02KY](https://kerodon.net/tag/02KY)）。対応表の状態：なし。

InitialBoundaryLifting.isInitialVertex\_fiberは一つの相対始頂点のfiber内での始対象性。原文の余錐全体のfiber内の余極限性へのcoslice・fiber交換の比較が引用の可換式だけからは得られない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting.isInitialVertex_fiber`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanRelativeCoconeRestriction_fiber_comparison`

:::

:::definition "kerodon_7_1_7_9"
Kerodon Definition 7.1.7.9（[Tag 069U](https://kerodon.net/tag/069U)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：相対余極限性の述語は全体の coslice に基づく。出る全辺 e の Δ¹×\_C E 上での余極限を量化した定義は見つからない。

:::

:::proposition "kerodon_7_1_7_14"
Kerodon Proposition 7.1.7.14（[Tag 05J6](https://kerodon.net/tag/05J6)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：個別のファイバーの相対始性を全空間へ移す境界充填補題はある。出る各辺上での余極限条件との iff は見つからない。

:::

:::corollary "kerodon_7_1_7_15"
Kerodon Corollary 7.1.7.15（[Tag 069Z](https://kerodon.net/tag/069Z)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：相対始頂点をファイバー内の始頂点に移す。locally cartesian な仮定で指定ファイバー図式の余極限性を相対余極限性と比較する型は見つからない。

:::

:::corollary "kerodon_7_1_7_16"
Kerodon Corollary 7.1.7.16（[Tag 06A0](https://kerodon.net/tag/06A0)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：全空間の相対余極限性の定義はある。ファイバー内の余極限と各辺の輸送による保存の連言を使う iff は見つからない。

:::

:::proposition "kerodon_7_1_7_18"
Kerodon Proposition 7.1.7.18（[Tag 02X6](https://kerodon.net/tag/02X6)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：相対始頂点に関する単一の引き戻しは扱う。二つの引き戻しと cartesian な対角を仮定して相対余極限を G で運ぶ型は見つからない。

:::

# 7.1.8 Limits and Colimits in Diagram ∞-Categories

%%%
number := false
tag := "kerodon-7-1-8"
%%%

Kerodon [Tag 02X8](https://kerodon.net/tag/02X8)

:::definition "kerodon_7_1_8_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsPointwiseColimitCone, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsPointwiseLimitCone, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.evaluateFunctorCone")
Kerodon Definition 7.1.8.1（[Tag 05QF](https://kerodon.net/tag/05QF)）。対応表の状態：本体にある。

仮定：内部 Hom B⟹C への K 上の図式と錐または余錐。型は C の Quasicategory を要求しない（Lean が弱い）。結論：全頂点 b で評価した各錐・余錐の極限性・余極限性を要求（原文と一致）。

:::

:::proposition "kerodon_7_1_8_2" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.hasColimit_of_hasPointwiseColimits, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isColimitCone_iff_pointwise_of_hasPointwiseColimits, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isLimitCone_iff_pointwise_of_hasPointwiseLimits")
Kerodon Proposition 7.1.8.2（[Tag 05QG](https://kerodon.net/tag/05QG)）。対応表の状態：本体にある。

仮定：Quasicategory C。Lean は一図式の各点での余極限だけを要求し、原文の C の K-余完備性より弱い（Lean が弱い）。結論：関手圏の HasColimit と、指定余錐の IsColimitCone↔IsPointwiseColimitCone。評価での保存もその順方向（原文と一致）。

:::

:::proposition "kerodon_7_1_8_3" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.exists_pointwiseColimitCone, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.hasColimit_of_hasPointwiseColimits, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isPointwiseLimitCone_of_isLimitCone_of_hasPointwiseLimits, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isColimitCone_iff_pointwise_of_hasPointwiseColimits") (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_7_1_3_19, kerodon_7_1_8_9, kerodon_7_1_8_15")
Kerodon Proposition 7.1.8.3（[Tag 02X9](https://kerodon.net/tag/02X9)）。対応表の状態：本体にある。

hasColimit\_of\_hasPointwiseColimitsは原文(1)、現本体のisColimitCone\_iff\_pointwise\_of\_hasPointwiseColimitsは同じ指定余錐の原文(2)のiffを直接返す。両者を合わせれば結論全体で、従来引用の極限側の補題は不要。

:::

:::corollary "kerodon_7_1_8_4"
Kerodon Corollary 7.1.8.4（[Tag 06A2](https://kerodon.net/tag/06A2)）。対応表の状態：一部。

FをcurryしたfにhasColimit\_of\_hasPointwiseColimitsとisColimitCone\_iff\_pointwise\_of\_hasPointwiseColimitsを適用すると、原文(1)と(2)を同じ関手圏で直接得る。(3)の二段余極限と全体の余極限の比較は含まない。通常圏のFubini同型をその∞圏版と同一視しない。

宣言：`CategoryTheory.Limits.colimitIsoColimitCurryCompColim`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isColimitCone_iff_pointwise_of_hasPointwiseColimits`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.hasColimit_of_hasPointwiseColimits`

:::

:::proposition "kerodon_7_1_8_5"
Kerodon Remark 7.1.8.5（[Tag 06A3](https://kerodon.net/tag/06A3)）。対応表の状態：なし。

MathlibのFubini同型は通常圏の余極限。同じnerve上の∞圏の二段余極限との比較がなく、通常圏の類似公式だけを特殊形として数えない。

宣言：`CategoryTheory.Limits.colimitIsoColimitCurryCompColim`

:::

:::corollary "kerodon_7_1_8_6"
Kerodon Corollary 7.1.8.6（[Tag 06A4](https://kerodon.net/tag/06A4)）。対応表の状態：なし。

MathlibのIsColimitは通常圏の積添字の図式。原文の任意単体形状での∞圏の余極限存在と同じ対象・錐であるnerve比較がない。

宣言：`CategoryTheory.Limits.isColimitCoconeOfHasColimitCurryCompColim`

:::

:::proposition "kerodon_7_1_8_7" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_1_4_1, kerodon_7_1_5_17, kerodon_7_1_6_13")
Kerodon Proposition 7.1.8.7（[Tag 06A5](https://kerodon.net/tag/06A5)）。対応表の状態：なし。

一般の部分複体の初頂点境界充填の持ち上げはあるが、原文の指定積・pushoutからの射を相対cocone制限の問題へ移す比較と同じf上での等式を引用型に持たない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.exists_lift_of_initial_first_vertices`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.exists_lift_of_terminal_last_vertices`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.exists_pointwiseLimitCone`

:::

:::corollary "kerodon_7_1_8_8"
Kerodon Corollary 7.1.8.8（[Tag 02XG](https://kerodon.net/tag/02XG)）。対応表の状態：なし。

点ごとの相対cocone充填をFunctor圏へ移す型と一般の持ち上げ型だけでは、原文の各bに指定された余錐f\_bを厳密に保つ同じ全体の持ち上げを直接返さない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.exists_lift_of_initial_first_vertices`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanRelativeCoconeLifting_functor_of_pointwise`

:::

:::corollary "kerodon_7_1_8_9" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.exists_pointwiseColimitCone, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.exists_pointwiseLimitCone")
Kerodon Corollary 7.1.8.9（[Tag 02XJ](https://kerodon.net/tag/02XJ)）。対応表の状態：本体にある。

仮定：Quasicategory C と全頂点で余極限を持つ図式 p:K→(B⟹C)（Kerodon と一致）。結論：IsPointwiseColimitCone を持つ延長 c の存在（原文と一致）。

:::

:::proposition "kerodon_7_1_8_10" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_1_3_2, kerodon_4_1_4_1, kerodon_4_4_5_3, kerodon_4_5_1_16, kerodon_4_5_3_33, kerodon_7_1_5_17, kerodon_7_1_6_13, kerodon_7_1_8_7")
Kerodon Proposition 7.1.8.10（[Tag 02XK](https://kerodon.net/tag/02XK)）。対応表の状態：一部。

Fをinner fibrationに強めると各F-colimitをKanRelativeCoconeLiftingへ移せ、relativeFunctor\_of\_first\_verticesが同じ相対内部Hom比較πで充填性を返す。πもinnerなので同じF′-colimitへ戻る。任意Fの場合は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanRelativeCoconeLifting_relativeFunctor_of_first_vertices`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialBoundaryLifting_ihom_of_pointwise`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.terminalBoundaryLifting_coneRestriction_of_pointwise`

:::

:::corollary "kerodon_7_1_8_11" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_7_1_8_10")
Kerodon Corollary 7.1.8.11（[Tag 02XM](https://kerodon.net/tag/02XM)）。対応表の状態：なし。

引用の射sj.πはUを含む相対内部Hom比較。原文の単なるpre(A⊆B)への相対余極限性と同じ射に同定する型を欠く。点ごとの絶対充填を移す補題だけではこの指定相対結論は直接出ない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanRelativeCoconeLifting_relativeFunctor_of_first_vertices`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialBoundaryLifting_coconeRestriction_of_pointwise`

:::

:::definition "kerodon_7_1_8_13" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1")
Kerodon Definition 7.1.8.13（[Tag 06A7](https://kerodon.net/tag/06A7)）。対応表の状態：一部。

Fをinner fibrationに制限すると引用のhfの型は全bで同じ評価余錐がF-colimitであるという原文の条件をそのまま表す。inlineの∀で表すこと自体は不足としない。任意Fの条件全体は引用の型の範囲外。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanIsRelativeColimitCone_functor_of_pointwise`

:::

:::corollary "kerodon_7_1_8_14"
Kerodon Corollary 7.1.8.14（[Tag 02XN](https://kerodon.net/tag/02XN)）。対応表の状態：一部。

Fをinner fibrationに強めるとkanIsRelativeColimitCone\_functor\_of\_pointwiseは同じ後合成F\^Bと転置余錐について原文の相対余極限性を直接返す。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanIsRelativeColimitCone_functor_of_pointwise`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanRelativeCoconeLifting_functor_of_pointwise`

:::

:::corollary "kerodon_7_1_8_15" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isColimitCone_of_pointwise, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isLimitCone_of_pointwise, SerrePositivity.KST.SConstruction.isInitialVertex_functorVertex_of_pointwise")
Kerodon Corollary 7.1.8.15（[Tag 02XP](https://kerodon.net/tag/02XP)）。対応表の状態：本体にある。

仮定：Quasicategory C と内部 Hom 上の余錐が全頂点で IsPointwiseColimitCone（Kerodon と一致）。結論：その余錐は関手圏で IsColimitCone（原文と一致）。

:::

# 7.1.9 Colimits and Categorical Pullback Squares

%%%
number := false
tag := "kerodon-7-1-9"
%%%

Kerodon [Tag 06A8](https://kerodon.net/tag/06A8)

:::proposition "kerodon_7_1_9_1" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1")
Kerodon Proposition 7.1.9.1（[Tag 06AA](https://kerodon.net/tag/06AA)）。対応表の状態：一部。

四角を厳密pullback、一方をEquivalenceLiftingとし、両側の全小余極限と両関手の保存を仮定すると、引用は同じpullback図式の余極限の存在と両射影の成分判定を直接返す。categorical pullback一般・Kだけの仮定ではない。原文第一結論の印字はC、型の結論はC₀₁なのでこの部分は一致と数えない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.pullback_hasSmallColimits`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.exists_colimitCone_pullback_with_snd`

:::

:::lemma_ "kerodon_7_1_9_2" (uses := "kerodon_1_4_0_1, kerodon_4_6_4_1, kerodon_7_1_7_6")
Kerodon Lemma 7.1.9.2（[Tag 06AC](https://kerodon.net/tag/06AC)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：普通の関手圏での点ごとの余極限判定はある。向き付きファイバー積で一方の合成が余極限のときに二射影で判定する型は見つからない。

:::

:::lemma_ "kerodon_7_1_9_3" (uses := "kerodon_1_4_0_1, kerodon_7_1_6_11, kerodon_7_1_9_2")
Kerodon Lemma 7.1.9.3（[Tag 06AD](https://kerodon.net/tag/06AD)）。対応表の状態：一部。

原文の三条件にF₁∘ev₁による同じ余錐の余極限性も追加するとisColimitCone\_laxPullback\_of\_componentsは同じoriented fiber productの余極限性を直接返す。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isColimitCone_laxPullback_of_components`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isColimitCone_laxPullback_iff_components`

:::

:::proposition "kerodon_7_1_9_4" (uses := "kerodon_1_4_0_1, kerodon_7_1_6_20, kerodon_7_1_9_3")
Kerodon Proposition 7.1.9.4（[Tag 06AE](https://kerodon.net/tag/06AE)）。対応表の状態：一部。

F₁側の選んだ余極限も保存されると追加すればexists\_colimitCone\_laxPullback\_with\_componentsは同じqの余極限と両成分が指定余錐となる等式を直接返す。追加保存なしの存在と任意延長のiff全体は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.exists_colimitCone_laxPullback_with_components`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.hasColimit_laxPullback_of_components`

:::

:::corollary "kerodon_7_1_9_5" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1")
Kerodon Corollary 7.1.9.5（[Tag 06AF](https://kerodon.net/tag/06AF)）。対応表の状態：一部。

Kを有限に限り、両側が全有限余極限を持ちF₀,F₁両方が保存すると強めれば、hasFiniteColimits\_laxPullback\_of\_preservationと有限成分判定は原文と同じoriented fiber productについて存在とiffを直接返す。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.hasFiniteColimits_laxPullback_of_preservation`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isColimitCone_laxPullback_iff_finite_components`

:::

:::corollary "kerodon_7_1_9_7" (uses := "kerodon_1_4_0_1, kerodon_7_1_9_4")
Kerodon Corollary 7.1.9.7（[Tag 06AH](https://kerodon.net/tag/06AH)）。対応表の状態：なし。

引用の対象は一方がisofibrationの厳密pullback。原文のhomotopy fiber productとの比較同値・指定図式をその比較に沿って移す型が引用にないため、別模型の類似としてnone。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.exists_colimitCone_pullback_with_snd`

:::

:::proposition "kerodon_7_1_9_8" (uses := "kerodon_1_4_0_1, kerodon_7_1_9_7")
Kerodon Proposition 7.1.9.8（[Tag 06AJ](https://kerodon.net/tag/06AJ)）。対応表の状態：一部。

四角を厳密IsPullback、F₀をinner fibrationに強めればisColimitCone\_of\_isPullback\_of\_componentsは原文の成分条件から同じqbarが余極限という方向を直接返す。一般categorical pullbackでの存在とiff全体は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isColimitCone_of_isPullback_of_components`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.pullback_isColimitCone_iff_components`

:::

:::proposition "kerodon_7_1_9_9"
Kerodon Proposition 7.1.9.9（[Tag 06AL](https://kerodon.net/tag/06AL)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Kan 複体の塔の空間圏での極限は扱う。isofibration の∞圏の塔で各段の指定余極限を両立させる型は見つからない。

:::

:::corollary "kerodon_7_1_9_10"
Kerodon Corollary 7.1.9.10（[Tag 06AM](https://kerodon.net/tag/06AM)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：二脚の厳密引き戻しで小余極限の存在を扱う。isofibration の塔の極限に任意の固定形状の余極限を移す型は見つからない。

:::

# 7.1.10 Colimits in ∞-Categories of Sections

%%%
number := false
tag := "kerodon-7-1-10"
%%%

Kerodon [Tag 06AN](https://kerodon.net/tag/06AN)

:::proposition "kerodon_7_1_10_1"
Kerodon Proposition 7.1.10.1（[Tag 06AP](https://kerodon.net/tag/06AP)）。対応表の状態：なし。

Fun(C,D)の点ごとの余極限と相対内部Hom後合成はあるが、原文の指定section空間をtrivial bundleのFunctor空間へ比較する同型を引用型に含まない。別対象の結果としてnone。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isColimitCone_iff_pointwise_of_hasPointwiseColimits`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.hasColimit_of_hasPointwiseColimits`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanIsRelativeColimitCone_functor_of_pointwise`

:::

:::corollary "kerodon_7_1_10_2"
Kerodon Corollary 7.1.10.2（[Tag 06AQ](https://kerodon.net/tag/06AQ)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：全関手圏の各点での余極限から HasColimit を得る。局所 cartesian な非定値ファイバー上の切断と評価に関する主張は見つからない。

:::

:::corollary "kerodon_7_1_10_3"
Kerodon Corollary 7.1.10.3（[Tag 06AR](https://kerodon.net/tag/06AR)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：定値ファイバーに当たる全関手圏の iff はある。辺に沿う輸送が各余極限を保つ仮定での非定値版は見つからない。

:::

:::corollary "kerodon_7_1_10_4"
Kerodon Corollary 7.1.10.4（[Tag 06AS](https://kerodon.net/tag/06AS)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：相対余極限の述語はある。各ファイバーの余極限が edgewise であることを仮定して、全切断の余極限を作る型は見つからない。

:::

:::corollary "kerodon_7_1_10_5"
Kerodon Corollary 7.1.10.5（[Tag 06AT](https://kerodon.net/tag/06AT)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：小余完備性を図式ごとに量化する述語はある。全ファイバーの固定 K-余完備性から locally cartesian な切断の余完備性を得る型は見つからない。

:::

:::corollary "kerodon_7_1_10_7"
Kerodon Corollary 7.1.10.7（[Tag 06AV](https://kerodon.net/tag/06AV)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：小余極限保存はある。各辺の輸送による K-余極限保存から切断の K-余完備性と点ごとの判定を得る型は見つからない。

:::

:::lemma_ "kerodon_7_1_10_8"
Kerodon Lemma 7.1.10.8（[Tag 06AW](https://kerodon.net/tag/06AW)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：全関手圏では点ごとの余極限性から余極限性を得る。inner fibration 上の切断の評価で edgewise 条件を使う版は見つからない。

:::

