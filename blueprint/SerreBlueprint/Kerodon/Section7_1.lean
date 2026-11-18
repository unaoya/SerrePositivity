import Verso
import VersoManual
import VersoBlueprint
import Mathlib.CategoryTheory.Limits.Fubini
import Mathlib.CategoryTheory.Limits.IsLimit
import SerrePositivity.InfinityCategories.HTT.InitialAndFinalObjects.InitialBoundaryTransport
import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.Definition
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.FiniteCoproductSiftedPreservation
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableEquivalence
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.EquivalenceSmallLimits
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.AdjunctionLimits
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CartesianInitialBoundary
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ChosenColimitAdjunction
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ChosenColimitFunctor
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CocartesianTerminalBoundary
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.Cocone
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ColimitDiagramIso
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConservativeLimitReflection
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConstantFunctor
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoreLimit
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CosliceLimitConeLift
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.EquivalenceAllLimits
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.EquivalenceColimitCones
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.FiniteLimitsColimits
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.FullyFaithfulConeReflection
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.FunctorConeTerminalBoundary
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.FunctorInitialBoundary
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.FunctorLimits
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.FunctorPointwiseColimitExistence
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.FunctorPointwiseColimits
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.FunctorPointwiseLimitCriterion
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.FunctorPointwiseLimitExistence
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryFiberRestriction
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.LaxPullbackCoconeComponentCriterion
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.LaxPullbackColimitConeExistence
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.LaxPullbackColimitCriterion
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.LaxPullbackFiniteColimits
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.LeftAdjointAllColimitPreservation
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.LeftCanonicalRestriction
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.LimitConeFamilyAdjunctionComparison
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.LimitDiagramIso
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.PullbackColimitConeExistence
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.PullbackSmallColimits
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.PullbackSquareCoconeCriterion
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ReflectionSmallColimits
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ReflectionSmallLimits
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ReflectiveModelLimitDetection
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeCoconeAbsolute
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeCoconeCriterion
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeCoconeInterchange
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeCoconeRestriction
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeColimit
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeColimitPointwise
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeColimitTrivialComparison
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeInitialBoundary
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeInitialBoundaryCriterion
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeInitialCosliceComparison
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeInitialFiberTransfer
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeInitialVertexIso
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeLimit
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.SliceOverColimitCreation
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.SliceOverSmallColimits
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.SquareFunctorTransport
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalBoundaryTransport
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.ConeIteratedSliceIso
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.EquivalenceLimits
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TerminalTransport
import SerrePositivity.KST.SConstruction.FunctorInitialVertices
import SerrePositivity.KST.SConstruction.RelativeUniversalityComposition

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "7.1 Limits and Colimits" =>
%%%
number := false
tag := "kerodon-7-1"
%%%

Kerodon の 7.1 節（[Tag 02H1](https://kerodon.net/tag/02H1)）の項目と、SerrePositivity・Mathlib の宣言との対応。本文は対応表（research/kerodon-coverage）の判定の理由の要約で、Kerodon の本文の写しではない。

*f-b-literature-yoneda.html — 2. Kerodon 第 7 章の内容*

- 節　／　内容
- 7.1 極限と余極限　／　定義（スライスの終対象）と形式的性質。定数図式、極限を保つこと、相対的な始・終対象と極限、関手 ∞ 圏の中の極限、categorical pullback との関係、切断の ∞ 圏の中の余極限
- 7.2 cofinality　／　left cofinal な写像に沿った制限は極限を変えない（7.2.2.11）。∞ 版 Quillen の定理 A（7.2.3.1）
- 7.3 Kan 拡張　／　一般の関手・包含・fibration に沿った Kan 拡張、相対版、存在、普遍性（7.3.6）、推移性。cartesian fibration 上の極限はファイバーごとの極限の極限（7.3.4.4、7.3.8.26）
- 7.4 空間の極限・余極限　／　次の表
- 7.5 ホモトピー極限・余極限　／　厳密な図式の Bousfield–Kan ホモトピー極限と ∞ 極限の比較。weighted nerve と 7.4 を使う。ホモトピー極限図式と categorical な極限図式の比較
- 7.6 例　／　積、引き戻し、イコライザー、列の極限、完備性。任意の極限は積とイコライザーから作れる（7.6.4.25、7.6.6.15）
- 7.7 余極限の普遍性　／　cartesian 自然変換、降下図式、cartesian 閉、交わらない余積、Mather の立方体定理、空間での降下、極限と余極限の交換（7.7.7）

7.4 は、一般の定義で定まる極限・余極限が $`\mathcal S` と $`\mathrm{Cat}_\infty`（Kerodon の $`\mathcal{QC}`）では具体的に何になるかを、図式を fibration に置き換えて求める節。第 5 章の分類定理（5.6）が前提になる。

- 小節　／　図式　／　具体形
- 7.4.1　／　$`C\to\mathcal S` の極限　／　分類する左 fibration の切断の空間 $`\mathrm{Fun}_{/C}(C,E)`（7.4.1.6）
- 7.4.2　／　—　／　分類を $`h\mathrm{Fun}(C,\mathcal S)\simeq h\mathrm{LFib}(C)` に引き上げる（7.4.2.4）
- 7.4.3　／　$`C\to\mathcal S` の余極限　／　全空間を Kan 化したもの（7.4.3.1）
- 7.4.4　／　$`C\to\mathrm{Cat}_\infty` の極限　／　cocartesian な切断の ∞ 圏（7.4.4.6）
- 7.4.5　／　$`C\to\mathrm{Cat}_\infty` の余極限　／　全空間を cocartesian 辺で局所化したもの（7.4.5.13）

1 圏では、集合値なら極限は Grothendieck 構成の切断の集合、余極限はその $`\pi_0`。$`\mathrm{Cat}` 値なら cocartesian な切断の圏と、cocartesian 射での局所化。$`\mathcal S` の余極限で $`\pi_0` の代わりに全空間そのものになるのが ∞ 版の特徴。7.4.4・7.4.5 は第 6 章 §8 で「Cat∞ 値の straightening が使われる」とした場面にあたる。7.7.7 は形式化で未完成と書かれていた filtered 余極限と有限極限の交換に関係する。

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

*02-mapping-limits.html — 5. 極限 — 定義の復習と一意性*

- \`isLimitCone\_iff\_trivialKanFibration\`：$`c` が極限錐 ⇔ $`(X_{/p})_{/c}\to X_{/p}` が trivial Kan fibration

- \`limitConeIso\`、\`limitVertexIso\`：二つの極限錐は $`h(X_{/p})` で同型で、頂点は $`hX` で同型

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

:::proposition "kerodon_7_1_1_13" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.limitVertexIso, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.limitConeIso, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.isLimitCone_iff_of_vertexIso") (uses := "kerodon_1_4_0_1")
Kerodon Proposition 7.1.1.13（[Tag 02JH](https://kerodon.net/tag/02JH)）。対応表の状態：一部。

limitVertexIsoは原文のX,Yがともに同じuの極限ならX≅Yという極限側の向きを直接返す。任意の同型な頂点に極限錐を厳密に持ち上げる逆は含まない。

:::

:::definition "kerodon_7_1_1_14" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.limitVertexIso, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitVertexIso")
Kerodon Notation 7.1.1.14（[Tag 02JJ](https://kerodon.net/tag/02JJ)）。対応表の状態：一部。

limitVertexIsoとcolimitVertexIsoは原文のlim/colimの同型類が図式だけで定まるという一意性を直接与える。任意の存在証明からの記法としての選択は含まない。

:::

:::definition "kerodon_7_1_1_15" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit, SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallLimits")
Kerodon Definition 7.1.1.15（[Tag 02JK](https://kerodon.net/tag/02JK)）。対応表の状態：一部。

HasLimitを全p:K→Cで量化すると原文のK-indexed limitsの条件を直接表す。名前付き述語の有無は理由とせず、colimits側は引用にないため数えない。

:::

:::definition "kerodon_7_1_1_16" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits, SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallLimits, SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits")
Kerodon Variant 7.1.1.16（[Tag 0390](https://kerodon.net/tag/0390)）。対応表の状態：一部。

HasFiniteLimits・HasSmallLimits・HasSmallColimitsはそれぞれ原文の有限極限・小極限・小余極限の存在条件を直接表す。有限余極限と任意の形状族の全定義は含まない。

:::

:::definition "kerodon_7_1_1_18" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.chosenColimitFunctor") (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_6_2_1_19")
Kerodon Definition 7.1.1.18（[Tag 05Q9](https://kerodon.net/tag/05Q9)）。対応表の状態：一部。

constantFunctorMapは原文の同じ対角δの実際の射を直接構成する。任意Tの左右随伴によるlimit/colimit functorという二つの述語全体は引用のchosenColimitFunctorだけからは得ない。

:::

:::proposition "kerodon_7_1_1_19" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.chosenColimitAdjunction, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneFamilyAdjunctHom_isIso")
Kerodon Proposition 7.1.1.19（[Tag 02JL](https://kerodon.net/tag/02JL)）。対応表の状態：一部。

chosenColimitAdjunctionは全てのK図式の余極限が存在すれば同じ対角に左随伴が存在するという余極限側の方向を直接返す。極限側と逆は含まない。

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

*定義 9.1 （極限と余極限）*

$`C` を quasicategory、$`K` を単体的集合、$`p\colon K\to C` を射とする。定理 4.8 によりスライス $`C_{/p}` とコスライス $`C_{p/}`（定義 4.5）は quasicategory である。

*注意 （錐）*

$`C_{/p}` の頂点は、$`K` 上で $`p` となる射 $`\Delta^0\star K\to C`、つまり $`p` 上の錐である。極限はその中の終対象、余極限は $`C_{p/}` の頂点（$`K\star\Delta^0\to C`、余錐）の中の始対象である。

*f-a-basics.html — 4. 極限・随伴・随伴関手定理*

- *極限*（HTT 1.2.13.4）：$`\mathcal C_{/p}` の終対象。fat slice では $`\mathcal C^{/p}\cong\mathcal C\times_{\mathrm{Fun}(K,\mathcal C)}\mathrm{Fun}(K,\mathcal C)^{/p}` なので、すべての $`y` で $`\mathrm{Map}(y,L)\to\mathrm{Map}(\delta y,p)` がホモトピー同値、と言い換えられる。極限錐全体は空か可縮。

- *関手性*：極限錐全体の充満部分圏 $`\mathcal D\subseteq\mathrm{Fun}(K^{\triangleleft},\mathcal C)` から $`\mathrm{Fun}(K,\mathcal C)` への制限は trivial fibration（HTT 4.3.2.15）。切断の空間は可縮で、切断と頂点での評価の合成が $`\lim`。これは $`\delta` の右随伴。$`K` については cofinal（極限では coinitial）な写像で比較写像が同値。

- 随伴の定義　／　データ　／　他の定義を導くのに必要なもの
- 対応（HTT 5.2.2.1）：$`\Delta^1` 上の対応で cartesian かつ cocartesian　／　$`\mathcal M\to\Delta^1`　／　関手の取り出しに straightening（底 $`\Delta^1`）
- 単位変換（HTT 5.2.2.8）：$`\mathrm{Map}(Fc,d)\to\mathrm{Map}(c,Gd)` がホモトピー同値　／　$`F,G,\eta`　／　対応の定義へは straightening
- 三角恒等式をホモトピーを除いて（ホモトピー 2 圏の中、Riehl–Verity）　／　$`F,G,\eta,\varepsilon`　／　ホモトピー整合的随伴への持ち上げ定理
- 各点の普遍射：$`c\downarrow G=\mathcal C_{c/}\times_{\mathcal C}\mathcal D` が始対象を持つ　／　$`G` と各点の始対象　／　切断による関手化

*随伴関手定理*（HTT 5.5.2.9）：presentable の間で、右随伴を持つ ⇔ 小さい余極限を保つ。左随伴を持つ ⇔ accessible で小さい極限を保つ。述べるだけでも $`\mathcal S` と写像空間の関手性（米田）が避けられない（コンパクト性の定義に $`\mathrm{Map}(x,-)` が $`\mathcal S` で余極限を保つことが要る）。presentable を仮定しない版として Nguyen–Raptis–Schrade の一般随伴関手定理がある。

*f-b-literature-yoneda.html — 11. 極限の同値な定義と、その使いどころ — 11.1 定義の一覧*

$`C` は quasicategory、$`p\colon K\to C`、錐 $`\bar p\colon\Delta^0\star K\to C`（$`\bar p|_K=p`、錐点の値 $`X`）。余極限は双対。

- 　／　定義　／　種類
- (1)　／　$`\bar p` は $`C_{/p}` の終対象（HTT 1.2.13.4）　／　スライスの終対象
- (1')　／　fat slice $`C^{/p}` の終対象　／　(1) の変種（HTT 4.2.1.5 で同値）
- (2)　／　制限 $`C_{/\bar p}\to C_{/p}` は trivial Kan fibration　／　持ち上げ性質
- (2')　／　$`n\ge1` で、$`\{n\}\star K` 上 $`\bar p` となる $`\partial\Delta^n\star K\to C` は $`\Delta^n\star K` に延びる　／　(2) の horn 版
- (3)　／　各 $`Y` で $`\mathrm{Map}_C(Y,X)\to\mathrm{Map}(\delta Y,p)` がホモトピー同値　／　写像空間（表現可能性）
- (4)　／　$`\bar p` は $`K\subseteq K^{\triangleleft}` に沿った $`p` の右 Kan 拡張　／　Kan 拡張
- (5)　／　（すべての $`K` 型の極限があるとき）$`\lim` は $`\delta\colon C\to\mathrm{Fun}(K,C)` の右随伴　／　随伴（(3) を $`Y` について自然にしたもの）
- (6)　／　$`\lim p` は $`K\to\Delta^0` に沿った右 Kan 拡張　／　(4) の一点版

定義でなく計算公式：$`\mathcal S` では $`\lim F\simeq\mathrm{Fun}_{/K}(K,\mathrm{Un}\,F)`（Kerodon 7.4.1）。単体的モデル圏のホモトピー極限との一致（HTT 4.2.4.1）はモデル圏を使うので今の方針では使わない。

*f-b-literature-yoneda.html — 11. 極限の同値な定義と、その使いどころ — 11.2 (1)(2)(3) の正確な形*

- $`C_{/p}`：$`n` 単体は $`p` を延長する $`\Delta^n\star K\to C`。射影 $`C_{/p}\to C` は $`\Delta^n` への制限。

- $`\mathrm{Hom}^R_C(Y,X)=\{Y\}\times_CC_{/X}`、錐の空間 $`\mathrm{Cone}(Y,p):=\{Y\}\times_CC_{/p}`。

- $`D` の対象 $`x` が終対象 ⇔ すべての $`y` で $`\mathrm{Hom}^R_D(y,x)` が可縮。

- (3) は zigzag $`\mathrm{Hom}^R_C(Y,X)\xleftarrow{\sim}\{Y\}\times_CC_{/\bar p}\xrightarrow{r_Y}\mathrm{Cone}(Y,p)` の $`r_Y` がホモトピー同値、と読む。左は錐点への制限（補題 C で trivial fibration）。直観的には $`f\mapsto\bar p\circ f` だが、合成に選択が要るので zigzag で書く。

*f-b-literature-yoneda.html — 11. 極限の同値な定義と、その使いどころ — 11.3 補題*

- 補題　／　内容
- A（join の持ち上げ）　／　単射 $`A\subseteq B`、$`q\colon B\to C`。$`i\colon L\subseteq M` に対する $`C_{/q}\to C_{/q&#124;_A}` の持ち上げは $`(L\star B)\cup(M\star A)\subseteq M\star B` に沿った延長。$`i` が right anodyne か $`A\subseteq B` が left anodyne なら inner anodyne（HTT 2.1.2.3。生成元では join-horn の等式）
- B　／　右 fibration が trivial Kan fibration ⇔ ファイバーがすべて可縮（HTT 2.1.3.4）。⇐ が重い部分
- C　／　錐点への制限 $`C_{/\bar p}\to C_{/X}` は trivial fibration。A により $`\Delta^0\subseteq\Delta^0\star K` が left anodyne を言えばよく、$`\Delta^0\star\mathrm{sk}_kK` のフィルターで各段は $`\Lambda^{k+1}_0=(\Delta^0\star\partial\Delta^k)\cup\Delta^k\subseteq\Delta^{k+1}` に沿った押し出し

*f-b-literature-yoneda.html — 11. 極限の同値な定義と、その使いどころ — 11.4 (1) ⇔ (2)*

$`C_{/p}` 上の同型 $`(C_{/p})_{/\bar p}\cong C_{/\bar p}`：左辺の $`n` 単体は最後の頂点が $`\bar p` の $`\Delta^{n+1}\to C_{/p}`、すなわち $`K` 上 $`p`・$`\{n+1\}\star K` 上 $`\bar p` の $`\Delta^{n+1}\star K\to C`。右辺の $`n` 単体は $`\Delta^0\star K` 上 $`\bar p` の $`\Delta^n\star\Delta^0\star K\to C`。結合律で一致し、射影はどちらも $`\Delta^n\star K` への制限。$`D=C_{/p}` の $`D_{/\bar p}\to D` は右 fibration でファイバーが $`\mathrm{Hom}^R_D(y,\bar p)` なので、補題 B により (1) ⇔ (2)。(2) を補題 A で読むと $`(\partial\Delta^n\star\Delta^0)\cup\Delta^n=\partial\Delta^{n+1}` から (2')。

*f-b-literature-yoneda.html — 11. 極限の同値な定義と、その使いどころ — 11.5 (2) ⇔ (3)*

1. $`r\colon C_{/\bar p}\to C_{/p}` は右 fibration（補題 A で $`i=\Lambda^n_j\subseteq\Delta^n`、$`0<j\le n`）。

2. $`r` は $`C` 上の右 fibration どうしの写像。$`r_Y` は Kan 複体の間の右 fibration なので Kan fibration（HTT 2.1.3.3）で、$`e\in\mathrm{Cone}(Y,p)` 上の $`r` のファイバーと $`r_Y` のファイバーは同じ。

3. (2) ⇔ $`r` のファイバーがすべて可縮（補題 B）⇔ 各 $`r_Y` のファイバーがすべて可縮 ⇔ 各 $`r_Y` がホモトピー同値（Kan fibration の長完全列。ファイバーは各頂点上でとる）⇔ (3)（補題 C と 2-out-of-3）。

重いのは補題 B の ⇐ だけで、残りは join の組合せ論と持ち上げ。

*f-b-literature-yoneda.html — 11. 極限の同値な定義と、その使いどころ — 11.6 (3) の使いどころ*

- 場面　／　使い方
- 右随伴は極限を保つ　／　$`\mathrm{Map}(Y,GX)\simeq\mathrm{Map}(FY,X)\simeq\mathrm{Map}(\delta FY,p)\simeq\mathrm{Map}(\delta Y,Gp)`
- $`\delta\dashv\lim`　／　(3) を $`Y` について自然にしたもの
- 写像空間の極限公式　／　$`\mathrm{Map}(Y,\lim p)\simeq\lim_k\mathrm{Map}(Y,p(k))`。降下での $`\mathrm{Map}_{D(X)}` の計算、$`\mathrm{Map}_{\lim C_i}(x,y)\simeq\lim\mathrm{Map}_{C_i}(x_i,y_i)`、安定圏の長完全列
- 関手が極限を保つか　／　像の錐が (3) をみたすかを写像空間で確かめる
- 点ごとの Kan 拡張　／　各点の条件が (3) の形

(1)/(2) で済むもの：錐としての一意性（終対象の空間が可縮）、cofinal な前合成での不変性、関手圏の極限が各点で計算できること、Kan 拡張の存在の持ち上げへの帰着。

- (3) の段階　／　右辺　／　必要なもの
- join 版　／　$`\mathrm{Cone}(Y,p)`　／　持ち上げだけ（11.5）
- fat 版　／　$`\mathrm{Map}_{\mathrm{Fun}(K,C)}(\delta Y,p)`　／　join と fat slice の比較（HTT 4.2.1.5）。随伴との比較に必要
- 極限公式版　／　$`\lim_k\mathrm{Map}(Y,p(k))`　／　$`k\mapsto\mathrm{Map}(Y,p(k))` の関手性、つまり St の後

形式化では定義に (1) か (2) を採り、(3) の join 版をすぐ示せる特徴づけとし、fat 版と極限公式版は比較定理と St の後の定理とする。

*f-b-literature-yoneda.html — 11. 極限の同値な定義と、その使いどころ — 11.7 Kerodon の順番（随伴 → 極限 → Yoneda）の依存関係*

Kerodon は随伴（単位 $`\eta` と、各点で $`\mathrm{Hom}(FX,Y)\to\mathrm{Hom}(X,GY)` がホモトピー同値という条件）も極限も各点の写像空間の条件で定義するので、$`\mathrm{Map}` の関手性も関手版 Yoneda も要らない。表現可能性は $`C_{X/}\to C` の始対象で言い、使うのは fibration 版 Yoneda。依存は後ろ向きで、第 7 章が第 6 章を（右随伴は極限を保つ、Kan 拡張は制限の随伴）、第 8 章が第 6・7 章を（Yoneda 埋め込みが極限を保つ、前層の自由余完備性）使う。HTT は極限 → Yoneda → 随伴の順で、随伴を $`\Delta^1` 上の双 cartesian fibration で定義し性質の証明に Yoneda を使う。形式化の流れ「fibration 版 Yoneda → St → Map → 関手版 Yoneda」とは Kerodon の順番が噛み合う。

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

:::corollary "kerodon_7_1_3_3" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit")
Kerodon Corollary 7.1.3.3（[Tag 02W9](https://kerodon.net/tag/02W9)）。対応表の状態：一部。

HasLimitとIsLimitConeを展開すると同じslice C\_/uに終対象が存在するという原文(1)⇔(3)。oriented fiber productの条件(2)は含まない。

:::

:::definition "kerodon_7_1_3_4" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone")
Kerodon Definition 7.1.3.4（[Tag 02JM](https://kerodon.net/tag/02JM)）。対応表の状態：本体にある。

仮定：K 上の p と左 join からの延長 c。述語の形成自体は Quasicategory C を要求しない（Lean が弱い）。結論：IsLimitCone c は sliceOver p の頂点 c が IsTerminalVertex（原文と一致）。

*定義 9.1 （極限と余極限）*

- $`C_{/p}` の頂点で終対象（定義 8.3）であるものを $`p` の極限という。

:::

:::definition "kerodon_7_1_3_5" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone")
Kerodon Variant 7.1.3.5（[Tag 02JN](https://kerodon.net/tag/02JN)）。対応表の状態：本体にある。

仮定：K 上の p と右 join からの延長 d。述語の形成自体は Quasicategory C を要求しない（Lean が弱い）。結論：IsColimitCone d は sliceUnder p の頂点 d が IsInitialVertex（原文と一致）。

*定義 9.1 （極限と余極限）*

- $`C_{p/}` の頂点で始対象（定義 8.1）であるものを $`p` の余極限という。

:::

:::proposition "kerodon_7_1_3_15"
Kerodon Proposition 7.1.3.15（[Tag 06TF](https://kerodon.net/tag/06TF)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：任意の join 錐の極限性は定義される。終頂点の指示写像 Q で指定された立方体の制限を比較する極限判定は見つからない。

:::

:::proposition "kerodon_7_1_3_17" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isLimitCone_iff_trivialKanFibration, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coneIteratedSliceIso_restriction, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coneIteratedSliceIso") (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_4_3_6_12, kerodon_4_4_1_11, kerodon_4_5_6_20, kerodon_4_7_3_12, kerodon_5_1_6_4, kerodon_7_1_3_4")
Kerodon Proposition 7.1.3.17（[Tag 02JU](https://kerodon.net/tag/02JU)）。対応表の状態：一部。

coneIteratedSliceIso\_restrictionはC\_/cからC\_/pへの同じ制限射を(sliceOver p)\_/cの射影に同型で対応させる。isLimitCone\_iff\_trivialKanFibrationをこの同じ射に移せば原文(1)⇔(2)を直接得る。(3),(4)からの逆は含まない。

:::

:::proposition "kerodon_7_1_3_18" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone.of_functorIso, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone.of_functorIso") (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_4_4_4")
Kerodon Proposition 7.1.3.18（[Tag 0391](https://kerodon.net/tag/0391)）。対応表の状態：一部。

ρを全錐図式のFunctorIsoと強めるとIsLimitCone.of\_functorIsoは同じ全図式の極限性を移し、原文(1)⇒(2)を直接与える。K上の各成分だけの可逆性からの全二取三は含まない。

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

:::definition "kerodon_7_1_4_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone")
Kerodon Definition 7.1.4.1（[Tag 0392](https://kerodon.net/tag/0392)）。対応表の状態：一部。

mapJoinCone F cの極限性は原文前半の同じlimit diagramをFに後合成した極限性そのもの。専用のpreservedという述語名がないことは不足とせず、colimit側の構成は引用に含まない。

:::

:::definition "kerodon_7_1_4_4" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PreservesSmallLimits, SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits")
Kerodon Definition 7.1.4.4（[Tag 02JW](https://kerodon.net/tag/02JW)）。対応表の状態：一部。

PreservesSmallLimits/Colimitsを固定した小形状Kに評価すると、同じ図式・錐の後合成を保存する原文条件を直接得る。任意の大きさのKについての全定義ではない。

:::

:::definition "kerodon_7_1_4_5" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PreservesSmallLimits, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.PreservesFiniteCoproducts")
Kerodon Variant 7.1.4.5（[Tag 0395](https://kerodon.net/tag/0395)）。対応表の状態：一部。

PreservesSmallLimitsは原文の小極限保存の定義を直接表す。PreservesFiniteCoproductsは有限余積のみで有限余極限全体とはしない。

:::

:::proposition "kerodon_7_1_4_12" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsQCatEquivalence.isLimitCone_iff, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.QCatEquivalence.isLimitCone_iff, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.equivalence_isColimitCone_iff")
Kerodon Proposition 7.1.4.12（[Tag 02JZ](https://kerodon.net/tag/02JZ)）。対応表の状態：本体にある。

仮定：二つの quasicategory、F の IsQCatEquivalence と任意の K 上の錐・余錐（Kerodon と一致）。結論：各錐の極限性と F で写した錐の極限性の iff、余錐の双対の iff（原文と一致）。

*02-mapping-limits.html — 5. 極限 — 同値による保存*

*命題.* $`f\colon X\to Y` が同値なら、$`c` が極限錐であることと $`f\circ c` が極限錐であることは同値。

Lean では \`IsQCatEquivalence.isLimitCone\_iff\`（Core/EquivalenceAllLimits）。§4 と同じく path による置き換えを使う。同値の場合は $`\tilde X\to X` と $`\tilde X\to Y` がともに trivial Kan fibration になる。trivial Kan fibration $`q` については、slice の後合成 $`X_{/p}\to Y_{/qp}` も trivial Kan fibration（\`trivialKanFibration\_sliceOverPostcomp\`）なので、終対象性を保存・反映する。

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

:::corollary "kerodon_7_1_4_18" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsQCatEquivalence.isLimitCone_iff, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.hasLimit_iff_restrict_of_precompositionEquivalence")
Kerodon Corollary 7.1.4.18（[Tag 02K3](https://kerodon.net/tag/02K3)）。対応表の状態：一部。

与えられた極限錐cの存在証人にIsQCatEquivalence.isLimitCone\_iffの順方向を適用し、原文(1)の存在の順方向を直接得る。添字前合成の存在iffは終域同値の逆方向の代用にしない。

:::

:::corollary "kerodon_7_1_4_19" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.HasSmallLimits.of_equivalence, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.HasSmallColimits.of_equivalence")
Kerodon Corollary 7.1.4.19（[Tag 02K4](https://kerodon.net/tag/02K4)）。対応表の状態：一部。

C,Dの一方が全小極限／全小余極限を持つと強めればHasSmallLimits.of\_equivalenceとHasSmallColimits.of\_equivalenceは、同じ小形状Kについて他方の存在を直接与える。逆はe.symm。Kだけの存在からの一般の比較は含まない。

:::

:::proposition "kerodon_7_1_4_21" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isLimitCone_of_conservative_image")
Kerodon Proposition 7.1.4.21（[Tag 02K6](https://kerodon.net/tag/02K6)）。対応表の状態：一部。

原文のK-indexed limitsの存在から証人dを取り、保存性でhFdを得ればisLimitCone\_of\_conservative\_imageは同じcの像から極限性を反映する。順方向は入力の保存性であり、極限側のiff全体が直接従う。余極限側は含まない。

:::

:::lemma_ "kerodon_7_1_4_22" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isLimitCone_of_conservative_image") (uses := "kerodon_1_4_0_1, kerodon_4_4_2_12")
Kerodon Lemma 7.1.4.22（[Tag 02K7](https://kerodon.net/tag/02K7)）。対応表の状態：一部。

isLimitCone\_of\_conservative\_imageは原文と同じ保存された証人dと保守性の下で、F(c)が極限ならcが極限となる方向を直接返す。逆をこの引用型だけには含めない。

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

:::proposition "kerodon_7_1_4_26" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceOver_isColimitCone_iff_projection, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceOver_hasColimit_of_projection") (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_7_3_19, kerodon_7_1_3_17")
Kerodon Proposition 7.1.4.26（[Tag 02KB](https://kerodon.net/tag/02KB)）。対応表の状態：一部。

A=Δ⁰、fが頂点の場合、sliceOver\_hasColimit\_of\_projectionで余極限錐を取り、sliceOver\_isColimitCone\_iff\_projectionで同じ錐の像の余極限性を直接得る。原文(2)のこの場合のみで、一般Aと(1)は含まない。

:::

:::corollary "kerodon_7_1_4_27" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceOver_hasSmallColimits, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.exists_cosliceCone_lift_of_isLimit") (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_7_1_4_25, kerodon_7_1_4_26")
Kerodon Corollary 7.1.4.27（[Tag 02KC](https://kerodon.net/tag/02KC)）。対応表の状態：一部。

A=Δ⁰かつCが全小余極限を持つ場合、sliceOver\_hasSmallColimitsは同じsliceの各小Kの余極限存在を直接返す。一般Aでのcosliceの錐の持ち上げは極限性まで述べず、両側のiff全体は含まない。

:::

:::corollary "kerodon_7_1_4_28" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.mapJoinCone_isLimit_of_adjunction, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.mapJoinCocone_isColimit_of_adjunction")
Kerodon Corollary 7.1.4.28（[Tag 02KE](https://kerodon.net/tag/02KE)）。対応表の状態：本体にある。

仮定：二つの quasicategory と QCatAdjunction F G、任意の K（Kerodon と一致）。結論：G が極限錐を極限錐に、F が余極限錐を余極限錐に送る（原文と一致）。

:::

:::corollary "kerodon_7_1_4_29" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.hasSmallColimits_of_reflection, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.reflectiveSubcategory_hasSmallColimits")
Kerodon Corollary 7.1.4.29（[Tag 04JW](https://kerodon.net/tag/04JW)）。対応表の状態：一部。

Cが全小余極限を持つと強めればreflectiveSubcategory\_hasSmallColimitsは同じ反射的full subcategoryで指定の小図式uの余極限存在を直接与える。一図式だけの周囲での存在からの一般化は含まない。

:::

:::corollary "kerodon_7_1_4_31" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.reflectiveSubcategory_hasSmallColimits")
Kerodon Corollary 7.1.4.31（[Tag 06YB](https://kerodon.net/tag/06YB)）。対応表の状態：一部。

周囲のCが全小余極限を持つと強めると、reflectiveSubcategory\_hasSmallColimitsは同じ反射的部分圏について指定小Kの全図式の余極限存在を直接返す。

:::

:::definition "kerodon_7_1_4_33" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.reflective_isLimitCone_iff_inclusion, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.reflective_mem_limitCone, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.fullSubcomplex_hasLimit_of_apex")
Kerodon Variant 7.1.4.33（[Tag 04JX](https://kerodon.net/tag/04JX)）。対応表の状態：一部。

reflective\_isLimitCone\_iff\_inclusionは原文の既存極限錐の包含による保存・反映を直接与える。さらにPの同型閉性を加えるとmem\_limitConeとfullSubcomplex\_hasLimit\_of\_apexで同じ図式の存在も移る。任意Pの存在反映は含まない。

:::

:::lemma_ "kerodon_7_1_4_34" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.reflective_mem_limitCone")
Kerodon Lemma 7.1.4.34（[Tag 04JY](https://kerodon.net/tag/04JY)）。対応表の状態：一部。

部分圏をrepleteにも強めるとreflective\_mem\_limitConeの空添字の場合は同じ終頂点Xが部分圏に属すると直接返す。原文最後のrepleteの場合の結論に一致し、任意のreflective部分圏は含まない。

:::

:::corollary "kerodon_7_1_4_35" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.reflectiveSubcategory_hasSmallLimits, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.reflectiveSubcategory_hasSmallColimits")
Kerodon Corollary 7.1.4.35（[Tag 03Y1](https://kerodon.net/tag/03Y1)）。対応表の状態：一部。

周囲の全小極限／余極限の存在を加え、極限側はPの同型閉性も加えると、二つのreflectiveSubcategory\_hasSmall\*は同じ部分圏の指定小Kでの存在を直接返す。Kだけの存在の一般形ではない。

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

:::corollary "kerodon_7_1_5_11" (lean := "SerrePositivity.InfinityCategories.HTT.InitialAndFinalObjects.InitialBoundaryLifting.of_vertexIso, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalBoundaryLifting.of_vertexIso")
Kerodon Corollary 7.1.5.11（[Tag 02WP](https://kerodon.net/tag/02WP)）。対応表の状態：一部。

Uをinner fibrationに強め、相対始／終性をInitial/TerminalBoundaryLiftingで持つ場合、of\_vertexIsoと同じeのsymmを使えば指定頂点X,Yの両方向の移送を直接得る。任意のUの写像空間による相対性への比較は含まない。

:::

:::corollary "kerodon_7_1_5_12" (lean := "SerrePositivity.KST.SConstruction.relativeInitialVertexIso, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeInitialVertexIso") (uses := "kerodon_1_4_0_1, kerodon_7_1_5_10")
Kerodon Corollary 7.1.5.12（[Tag 02WQ](https://kerodon.net/tag/02WQ)）。対応表の状態：一部。

Uをinner fibration、相対始性をInitialBoundaryLiftingに強めると、relativeInitialVertexIsoは原文のU(X)≅U(Y)からX≅Yを同じ二頂点について直接返す。逆は頂点同型のmap。一般Uへの比較は含まない。

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

:::proposition "kerodon_7_1_5_16" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeCosliceMap_trivialKanFibration_of_initialBoundaryLifting") (uses := "kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_4_3_6_1, kerodon_4_6_5_10, kerodon_5_1_7_16")
Kerodon Proposition 7.1.5.16（[Tag 02WR](https://kerodon.net/tag/02WR)）。対応表の状態：一部。

Uをinner fibrationに強めると相対始性をInitialBoundaryLiftingへ移せ、relativeCosliceMap\_trivialKanFibration\_of\_initialBoundaryLiftingは原文(1)の同じ相対coslice比較を自明Kan、従って圏同値と直接返す。逆と相対終側は含まない。

:::

:::corollary "kerodon_7_1_5_17" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanRelativeInitialVertex_iff_initialBoundary, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeCosliceMap_trivialKanFibration_of_initialBoundaryLifting") (uses := "kerodon_1_4_0_1, kerodon_4_3_6_9, kerodon_4_5_6_20, kerodon_7_1_5_16")
Kerodon Corollary 7.1.5.17（[Tag 02WS](https://kerodon.net/tag/02WS)）。対応表の状態：一部。

kanRelativeInitialVertex\_iff\_initialBoundaryは原文(1)⇔(3)、相対cosliceの補題は(3)⇒(2)を同じU,Yで直接返す。三条件の全同値は含まない。

:::

:::corollary "kerodon_7_1_5_18" (uses := "kerodon_1_4_0_1, kerodon_7_1_5_17")
Kerodon Corollary 7.1.5.18（[Tag 02WT](https://kerodon.net/tag/02WT)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：自明 Kan ファイブレーションは一頂点からの coslice 比較に対するもの。相対始頂点の充満部分圏の制限とは異なる。

:::

:::proposition "kerodon_7_1_5_19" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialBoundaryLifting_fiber_of_total, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanInitialBoundaryLifting_of_fiber_map, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isTerminalVertex_fiber_iff_terminalBoundaryLifting") (uses := "kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_3_3_7_5, kerodon_4_6_1_22, kerodon_5_1_1_1, kerodon_5_1_3_11, kerodon_5_1_4_1")
Kerodon Proposition 7.1.5.19（[Tag 02WU](https://kerodon.net/tag/02WU)）。対応表の状態：一部。

Fもinner fibrationと強めれば、相対始性と境界充填のiffをFとfiberのF\_Eに適用できる。total→fiberとcartesian辺保存下のfiber→totalの二型が原文の同じ頂点の結論を返す。任意Fには及ばない。

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

:::corollary "kerodon_7_1_6_11" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanRelativeInitialVertex_comp_iff_of_fullyFaithful, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanIsRelativeColimitCone_comp_iff_of_trivialKanFibration") (uses := "kerodon_1_4_0_1, kerodon_7_1_6_10")
Kerodon Corollary 7.1.6.11（[Tag 02X5](https://kerodon.net/tag/02X5)）。対応表の状態：一部。

Vをtrivial Kan fibrationに強めればkanIsRelativeColimitCone\_comp\_iff\_of\_trivialKanFibrationは原文(2)の同じ余錐についてのiffを直接返す。一般の充満忠実Vと極限側は含まない。

:::

:::corollary "kerodon_7_1_6_12" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanIsColimitCone_of_relativeLifting_of_image, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanIsRelativeColimitCone_iff_isColimit_of_terminal") (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_7_1_6_10")
Kerodon Corollary 7.1.6.12（[Tag 02KR](https://kerodon.net/tag/02KR)）。対応表の状態：一部。

Uをinner fibrationに強め、相対余極限からKanRelativeCoconeLiftingへのiffを使えば、kanIsColimitCone\_of\_relativeLifting\_of\_imageは原文(2)の相対余極限と像の余極限から元の余極限を直接返す。極限側と逆は含まない。

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

*02-mapping-limits.html — 5. 極限 — 関手 ∞ 圏の極限は各点で計算できる*

*命題*（HTT Prop. 5.1.2.2、Kerodon §7.1.8）. 図式 $`p\colon J\to\mathrm{Fun}(K,X)` について：

1. 各点 $`k\in K` で評価した錐が極限錐なら、元の錐も極限錐（\`isLimitCone\_of\_pointwise\`）。

2. 各点で極限が存在するなら、各点で極限になる錐が存在する（\`exists\_pointwiseLimitCone\`）。したがって極限が存在する（\`hasLimit\_of\_hasPointwiseLimits\`）。

3. その状況では、極限錐であることと各点で極限錐であることは同値（\`isLimitCone\_iff\_pointwise\_of\_hasPointwiseLimits\`）。

2 の難しさは、各点で選んだ極限錐に自然性がないことにある。そこで「相対的な終点境界充填」を使い、選んだ錐を $`K` の単体に沿って一つずつ自然な族へ延長していく（Core/FunctorPointwiseLimitExistence）。

:::

:::corollary "kerodon_7_1_8_4" (lean := "CategoryTheory.Limits.colimitIsoColimitCurryCompColim, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isColimitCone_iff_pointwise_of_hasPointwiseColimits, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.hasColimit_of_hasPointwiseColimits")
Kerodon Corollary 7.1.8.4（[Tag 06A2](https://kerodon.net/tag/06A2)）。対応表の状態：一部。

FをcurryしたfにhasColimit\_of\_hasPointwiseColimitsとisColimitCone\_iff\_pointwise\_of\_hasPointwiseColimitsを適用すると、原文(1)と(2)を同じ関手圏で直接得る。(3)の二段余極限と全体の余極限の比較は含まない。通常圏のFubini同型をその∞圏版と同一視しない。

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

:::proposition "kerodon_7_1_8_10" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanRelativeCoconeLifting_relativeFunctor_of_first_vertices, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialBoundaryLifting_ihom_of_pointwise, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.terminalBoundaryLifting_coneRestriction_of_pointwise") (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_1_3_2, kerodon_4_1_4_1, kerodon_4_4_5_3, kerodon_4_5_1_16, kerodon_4_5_3_33, kerodon_7_1_5_17, kerodon_7_1_6_13, kerodon_7_1_8_7")
Kerodon Proposition 7.1.8.10（[Tag 02XK](https://kerodon.net/tag/02XK)）。対応表の状態：一部。

Fをinner fibrationに強めると各F-colimitをKanRelativeCoconeLiftingへ移せ、relativeFunctor\_of\_first\_verticesが同じ相対内部Hom比較πで充填性を返す。πもinnerなので同じF′-colimitへ戻る。任意Fの場合は含まない。

:::

:::corollary "kerodon_7_1_8_11" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_7_1_8_10")
Kerodon Corollary 7.1.8.11（[Tag 02XM](https://kerodon.net/tag/02XM)）。対応表の状態：なし。

引用の射sj.πはUを含む相対内部Hom比較。原文の単なるpre(A⊆B)への相対余極限性と同じ射に同定する型を欠く。点ごとの絶対充填を移す補題だけではこの指定相対結論は直接出ない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanRelativeCoconeLifting_relativeFunctor_of_first_vertices`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialBoundaryLifting_coconeRestriction_of_pointwise`

:::

:::definition "kerodon_7_1_8_13" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanIsRelativeColimitCone_functor_of_pointwise") (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1")
Kerodon Definition 7.1.8.13（[Tag 06A7](https://kerodon.net/tag/06A7)）。対応表の状態：一部。

Fをinner fibrationに制限すると引用のhfの型は全bで同じ評価余錐がF-colimitであるという原文の条件をそのまま表す。inlineの∀で表すこと自体は不足としない。任意Fの条件全体は引用の型の範囲外。

:::

:::corollary "kerodon_7_1_8_14" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanIsRelativeColimitCone_functor_of_pointwise, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanRelativeCoconeLifting_functor_of_pointwise")
Kerodon Corollary 7.1.8.14（[Tag 02XN](https://kerodon.net/tag/02XN)）。対応表の状態：一部。

Fをinner fibrationに強めるとkanIsRelativeColimitCone\_functor\_of\_pointwiseは同じ後合成F\^Bと転置余錐について原文の相対余極限性を直接返す。

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

:::proposition "kerodon_7_1_9_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.pullback_hasSmallColimits, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.exists_colimitCone_pullback_with_snd") (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1")
Kerodon Proposition 7.1.9.1（[Tag 06AA](https://kerodon.net/tag/06AA)）。対応表の状態：一部。

四角を厳密pullback、一方をEquivalenceLiftingとし、両側の全小余極限と両関手の保存を仮定すると、引用は同じpullback図式の余極限の存在と両射影の成分判定を直接返す。categorical pullback一般・Kだけの仮定ではない。原文第一結論の印字はC、型の結論はC₀₁なのでこの部分は一致と数えない。

:::

:::lemma_ "kerodon_7_1_9_2" (uses := "kerodon_1_4_0_1, kerodon_4_6_4_1, kerodon_7_1_7_6")
Kerodon Lemma 7.1.9.2（[Tag 06AC](https://kerodon.net/tag/06AC)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：普通の関手圏での点ごとの余極限判定はある。向き付きファイバー積で一方の合成が余極限のときに二射影で判定する型は見つからない。

:::

:::lemma_ "kerodon_7_1_9_3" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isColimitCone_laxPullback_of_components, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isColimitCone_laxPullback_iff_components") (uses := "kerodon_1_4_0_1, kerodon_7_1_6_11, kerodon_7_1_9_2")
Kerodon Lemma 7.1.9.3（[Tag 06AD](https://kerodon.net/tag/06AD)）。対応表の状態：一部。

原文の三条件にF₁∘ev₁による同じ余錐の余極限性も追加するとisColimitCone\_laxPullback\_of\_componentsは同じoriented fiber productの余極限性を直接返す。

:::

:::proposition "kerodon_7_1_9_4" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.exists_colimitCone_laxPullback_with_components, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.hasColimit_laxPullback_of_components") (uses := "kerodon_1_4_0_1, kerodon_7_1_6_20, kerodon_7_1_9_3")
Kerodon Proposition 7.1.9.4（[Tag 06AE](https://kerodon.net/tag/06AE)）。対応表の状態：一部。

F₁側の選んだ余極限も保存されると追加すればexists\_colimitCone\_laxPullback\_with\_componentsは同じqの余極限と両成分が指定余錐となる等式を直接返す。追加保存なしの存在と任意延長のiff全体は含まない。

:::

:::corollary "kerodon_7_1_9_5" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.hasFiniteColimits_laxPullback_of_preservation, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isColimitCone_laxPullback_iff_finite_components") (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1")
Kerodon Corollary 7.1.9.5（[Tag 06AF](https://kerodon.net/tag/06AF)）。対応表の状態：一部。

Kを有限に限り、両側が全有限余極限を持ちF₀,F₁両方が保存すると強めれば、hasFiniteColimits\_laxPullback\_of\_preservationと有限成分判定は原文と同じoriented fiber productについて存在とiffを直接返す。

:::

:::corollary "kerodon_7_1_9_7" (uses := "kerodon_1_4_0_1, kerodon_7_1_9_4")
Kerodon Corollary 7.1.9.7（[Tag 06AH](https://kerodon.net/tag/06AH)）。対応表の状態：なし。

引用の対象は一方がisofibrationの厳密pullback。原文のhomotopy fiber productとの比較同値・指定図式をその比較に沿って移す型が引用にないため、別模型の類似としてnone。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.exists_colimitCone_pullback_with_snd`

:::

:::proposition "kerodon_7_1_9_8" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isColimitCone_of_isPullback_of_components, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.pullback_isColimitCone_iff_components") (uses := "kerodon_1_4_0_1, kerodon_7_1_9_7")
Kerodon Proposition 7.1.9.8（[Tag 06AJ](https://kerodon.net/tag/06AJ)）。対応表の状態：一部。

四角を厳密IsPullback、F₀をinner fibrationに強めればisColimitCone\_of\_isPullback\_of\_componentsは原文の成分条件から同じqbarが余極限という方向を直接返す。一般categorical pullbackでの存在とiff全体は含まない。

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

