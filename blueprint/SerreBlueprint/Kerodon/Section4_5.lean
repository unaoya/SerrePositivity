import Verso
import VersoManual
import VersoBlueprint
import Mathlib.AlgebraicTopology.Quasicategory.StrictBicategory
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.FiberwiseHomPostInnerFibration
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.LeftFibrationFiberReflection
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.FiberwiseHomInnerFibration
import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.Equivalence
import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.WeakHomotopy
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.FibrationTower
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.CospanComparison
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedTowerTrivialFibration
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.DiscreteLimitComparison
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InverseSequenceQuasicategory
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.CatPullback
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalenceCalculus
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalenceLiftingPullback
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalenceLiftingTrivial
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePath
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePrismExtension
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePullbackPathLifting
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FiberwiseFunctor
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FiberwiseFunctorComponents
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FiberwiseHom
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorComposition
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.HomotopyQCat
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsofibrationCriterion
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.PrecompositionCellClosure
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.PrecompositionEquivalence
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.PrecompositionFiberEquivalence
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.PrecompositionHomotopy
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.PrecompositionLifting
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.PrecompositionMonoCobaseChange
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.PrecompositionPushoutGluing
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.PrecompositionPushoutProduct
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.PrecompositionRelativeLifting
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.PullbackMapComponentEquivalence
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.RelativeFunctorOverEquivalence
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.RelativeHomEquivalenceRestriction
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.ReplacementSpanComparison
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.TrivialFibrationEquivalence
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.WeightedTowerKan
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.RelativeInternalHomLifting
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.RelativeRestrictionLifting
import SerrePositivity.KST.Comparison.HomotopyPullbackThreeInputs
import SerrePositivity.KST.Spectra.ReedyWeightRestrictionFibration
import SerrePositivity.KST.Spectra.WeightedEndReedyKan

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "4.5 Equivalence" =>
%%%
number := false
tag := "kerodon-4-5"
%%%

Kerodon の 4.5 節（[Tag 01DE](https://kerodon.net/tag/01DE)）の項目と、SerrePositivity・Mathlib の宣言との対応。本文は対応表（research/kerodon-coverage）の判定の理由の要約で、Kerodon の本文の写しではない。

# 4.5.1 Equivalences of ∞-Categories

%%%
number := false
tag := "kerodon-4-5-1"
%%%

Kerodon [Tag 01DQ](https://kerodon.net/tag/01DQ)

*01-quasicategories.html — 6. ∞ 圏の同値 — 基本的な性質*

- 内容　／　Lean　／　場所
- 反射律・対称律・推移律　／　\`QCatEquivalence.refl\`／\`symm\`／\`trans\`　／　Core/Equivalence
- 同値 ⇒ $`hX\simeq hY`　／　\`QCatEquivalence.toHoEquivalence\`　／　同上
- 自然同型で不変、二対三　／　\`IsQCatEquivalence.ofFunctorIso\`、\`.comp\`、\`.cancel\_left\`、\`.cancel\_right\`　／　Core/EquivalenceCalculus
- 二対六　／　\`isQCatEquivalence\_of\_composites\`　／　Core/EquivalenceTwoOfSix
- 前合成・後合成で $`\mathrm{Fun}` の同値に　／　\`QCatEquivalence.precompose\`／\`postcompose\`　／　Core/FunctorComposition
- quasicategory 間の inner anodyne 射は同値　／　\`isQCatEquivalence\_of\_innerAnodyne\`　／　Core/InnerAnodyneEquivalence

*最後の項目の方針*：$`i\colon A\to B` が inner anodyne なら、制限 $`\mathrm{Fun}(B,Y)\to\mathrm{Fun}(A,Y)` は trivial Kan fibration になる（\`trivialKanFibration\_pre\_of\_innerAnodyne\`）。$`Y=A` とすると恒等射が持ち上がり、レトラクション $`r` で $`ri=\mathrm{id}` となるものが得られる。$`Y=B` とすると、$`\mathrm{id}_B` と $`ir` が同じ fiber に入ることから、可縮な fiber の中で両者を結ぶ可逆辺が得られる。

:::definition "kerodon_4_5_1_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.HomotopyQCat, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.homotopyQCatHomSetoid, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.homotopyQCat_category")
Kerodon Construction 4.5.1.1（[Tag 01DR](https://kerodon.net/tag/01DR)）。対応表の状態：本体にある。

仮定：同じ宇宙の ∞ 圏を対象とする（Kerodon と一致）。結論：HomotopyQCat の Hom は関手を hFun 内の同型で割った商。合成は元の写像の合成から降りる（一致）。

:::

:::proposition "kerodon_4_5_1_5"
Kerodon Proposition 4.5.1.5（[Tag 01DU](https://kerodon.net/tag/01DU)）。対応表の状態：なし。

Kan始域のrawな写像のcoreへの因子化はあるが、hQCat/hKanのHomの同じ商とその指定の包含による全単射の比較は型にない。商への降下の部品だけは数えない。

宣言：`SerrePositivity.KST.SConstruction.kanSourceCoreMap`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.kanCoreMap`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreLift`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorIso.core`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorIsoCoreHomotopy`

:::

:::corollary "kerodon_4_5_1_6"
Kerodon Corollary 4.5.1.6（[Tag 01DV](https://kerodon.net/tag/01DV)）。対応表の状態：なし。

quasicategoryCoreLift は対象ごとの因子化という部品。hQCatとhKanの指定包含の右随伴の型を直接構成しない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreLift`

:::

:::proposition "kerodon_4_5_1_8"
Kerodon Proposition 4.5.1.8（[Tag 01DX](https://kerodon.net/tag/01DX)）。対応表の状態：なし。

continuousKanReplacementとstrictKanCompletionはSSet上の置換関手。原文のhQCat/hKanの包含の左随伴へ降ろす比較と普遍性がさらに要る。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit_anodyne`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.strictKanCompletion`

:::

:::definition "kerodon_4_5_1_10" (lean := "SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence, SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence")
Kerodon Definition 4.5.1.10（[Tag 01DY](https://kerodon.net/tag/01DY)）。対応表の状態：本体にある。

仮定：Quasicategory X,Y と f:X→Y（Kerodon と一致）。結論：IsQCatEquivalence f は逆向きの関手と両合成の恒等への FunctorIso の存在。QCatEquivalence はデータを束ねる（一致）。

*01-quasicategories.html — 6. ∞ 圏の同値 — 定義*

Kerodon Def. 4.5.1.10 に従い、$`F\colon X\to Y` が*同値*であるとは、$`G\colon Y\to X` と、$`h\,\mathrm{Fun}(X,X)` での同型 $`GF\cong\mathrm{id}`、$`h\,\mathrm{Fun}(Y,Y)` での同型 $`FG\cong\mathrm{id}` が存在することとする。

\`\`\`text
abbrev FunctorIso \{X Y : SSet.\{u\}\} (f g : X ⟶ Y) :=
  (SSet.HomotopyCategory.mk (functorVertex f) : hoFunctor.obj ((ihom X).obj Y)) ≅
    SSet.HomotopyCategory.mk (functorVertex g)

structure QCatEquivalence (X Y : SSet.\{u\}) \[Quasicategory X\] \[Quasicategory Y\] where
  hom : X ⟶ Y
  inv : Y ⟶ X
  homInvIso : FunctorIso (hom ≫ inv) (𝟙 X)
  invHomIso : FunctorIso (inv ≫ hom) (𝟙 Y)

def IsQCatEquivalence ... (f : X ⟶ Y) : Prop :=
  ∃ g : Y ⟶ X, Nonempty (FunctorIso (f ≫ g) (𝟙 X)) ∧ Nonempty (FunctorIso (g ≫ f) (𝟙 Y))
\`\`\`

注意：\`FunctorIso\` は頂点ごとの同型の族ではない

\`FunctorIso f g\` は関手 ∞ 圏 $`\mathrm{Fun}(X,Y)` のホモトピー圏での同型であり、自然変換としての一貫性を含んでいる。「各点で可逆な自然変換は可逆」（Kerodon Thm. 4.4.4.4）はこれとは別の定理で、第 2 章で扱う（Core/FunctorEdgePointwise）。\`FunctorIso.toNatIso\` によってホモトピー圏の自然同型に落とせるが、逆は成り立たない。

:::

:::proposition "kerodon_4_5_1_16" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.QCatEquivalence.postcompose, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.QCatEquivalence.precompose, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorIso.map_post") (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1")
Kerodon Remark 4.5.1.16（[Tag 01HA](https://kerodon.net/tag/01HA)）。対応表の状態：一部。

QCatEquivalence.postcompose は原文に明記された、同値Fによる同じ内部Hom後合成の同値性を直接与える。hQCat上に束ねた関手の構成は含まない。

:::

:::proposition "kerodon_4_5_1_22" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsQCatEquivalence.postcompose") (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_4_5_1_16")
Kerodon Proposition 4.5.1.22（[Tag 032X](https://kerodon.net/tag/032X)）。対応表の状態：一部。

IsQCatEquivalence.postcompose は全てのXに対して同じ後合成の同値性を返し、原文(1)⇒(2)を直接与える。他の条件と逆向きは含まない。

:::

:::definition "kerodon_4_5_1_23" (lean := "SSet.QCat.strictBicategory, SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso")
Kerodon Construction 4.5.1.23（[Tag 02BZ](https://kerodon.net/tag/02BZ)）。対応表の状態：Mathlib にある。

仮定：対象は SSet.QCat（Kerodon と一致）。結論：Hom 圏を hFun とし、関手合成を与える Mathlib の strictBicategory。FunctorIso は同型を表す補助型（一致）。

:::

# 4.5.2 Minimal ∞-Categories

%%%
number := false
tag := "kerodon-4-5-2"
%%%

Kerodon [Tag 03T1](https://kerodon.net/tag/03T1)

:::definition "kerodon_4_5_2_1"
Kerodon Definition 4.5.2.1（[Tag 0575](https://kerodon.net/tag/0575)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：Kan の最小モデル・最小ファイブレーション・レトラクト・通常圏・skeletalを照合。A 上で恒等となる Fun(B,C) の同型の述語。FunctorIso は固定部分の条件を持たない。

:::

:::definition "kerodon_4_5_2_4"
Kerodon Definition 4.5.2.4（[Tag 03T2](https://kerodon.net/tag/03T2)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：Kan の最小モデル・最小ファイブレーション・レトラクト・通常圏・skeletalを照合。境界に相対的に同型な n 単体が等しいという極小性。Mathlib の Minimal は順序の極小元。

:::

:::lemma_ "kerodon_4_5_2_12" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_1_5_6_1")
Kerodon Lemma 4.5.2.12（[Tag 03T9](https://kerodon.net/tag/03T9)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：Kan の最小モデル・最小ファイブレーション・レトラクト・通常圏・skeletalを照合。極小な始域を持つ圏同値の単射性。全部分複体の包含の単射性とは仮定が異なる。

:::

:::proposition "kerodon_4_5_2_13" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_1_5_6_1, kerodon_4_4_5_9, kerodon_4_5_2_12")
Kerodon Proposition 4.5.2.13（[Tag 03TC](https://kerodon.net/tag/03TC)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：Kan の最小モデル・最小ファイブレーション・レトラクト・通常圏・skeletalを照合。両端が極小なら圏同値の単体写像自体が同型という主張。Quasicategory の同値は逆を同型までしか与えない。

:::

:::corollary "kerodon_4_5_2_14"
Kerodon Corollary 4.5.2.14（[Tag 03TE](https://kerodon.net/tag/03TE)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：Kan の最小モデル・最小ファイブレーション・レトラクト・通常圏・skeletalを照合。極小な二つの ∞ 圏について圏同値と厳密同型が同値。極小性の定義を使う候補がない。

:::

:::proposition "kerodon_4_5_2_15" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_1_5_6_1, kerodon_4_4_5_8")
Kerodon Proposition 4.5.2.15（[Tag 03TF](https://kerodon.net/tag/03TF)）。対応表の状態：なし。

通常圏のskeletonは対象の同型類についての骨格で、原文の単体の相対ホモトピーを使うminimal性の型ではない。nerveへの特殊化でもminimalとの比較がさらに要る。

宣言：`CategoryTheory.skeleton_isSkeleton`、`CategoryTheory.fromSkeleton`

:::

:::corollary "kerodon_4_5_2_16"
Kerodon Corollary 4.5.2.16（[Tag 03TG](https://kerodon.net/tag/03TG)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：Kan の最小モデル・最小ファイブレーション・レトラクト・通常圏・skeletalを照合。極小 ∞ 圏の厳密同型類と一般の圏同値類の全単射。HomotopyQCat の商は関手の同型類。

:::

# 4.5.3 Categorical Pullback Squares

%%%
number := false
tag := "kerodon-4-5-3"
%%%

Kerodon [Tag 032Y](https://kerodon.net/tag/032Y)

:::definition "kerodon_4_5_3_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.catPullback, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePath, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.catPullback_quasicategory")
Kerodon Construction 4.5.3.1（[Tag 032Z](https://kerodon.net/tag/032Z)）。対応表の状態：本体にある。

仮定：∞ 圏 A,B,C と p:A→C、q:B→C（Lean が弱い：catPullback の構成自体は任意の SSet）。結論：可逆辺の空間 equivalencePath C の両端評価に沿った引き戻し。三者が ∞ 圏なら結果も ∞ 圏（一致）。

:::

:::definition "kerodon_4_5_3_8" (uses := "kerodon_1_4_0_1")
Kerodon Definition 4.5.3.8（[Tag 0335](https://kerodon.net/tag/0335)）。対応表の状態：なし。

catPullbackとその極限錐は選択した比較先の構成。原文の任意の四角形についての特定の比較写像が圏同値という述語を直接与えない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.catPullback`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.catPullbackCone_isLimit`

:::

:::proposition "kerodon_4_5_3_11"
Kerodon Proposition 4.5.3.11（[Tag 0338](https://kerodon.net/tag/0338)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：厳密 pullback の特例・片側 isofibration・通常圏の iso commaを照合。Kan の正方形で categorical pullback とホモトピー引き戻しを同定する iff。Kan 置換の比較は categorical pullback を仮定しない。

:::

:::definition "kerodon_4_5_3_12" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_3_4_1_6, kerodon_4_5_4_4")
Kerodon Variant 4.5.3.12（[Tag 046L](https://kerodon.net/tag/046L)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：厳密 pullback の特例・片側 isofibration・通常圏の iso commaを照合。底の一点が Kan である categorical pullback から弱ホモトピー引き戻しを得る方向。Kan 置換補題の前提は別。

:::

:::proposition "kerodon_4_5_3_15" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_3_4_1_6, kerodon_4_5_1_22")
Kerodon Proposition 4.5.3.15（[Tag 033C](https://kerodon.net/tag/033C)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：厳密 pullback の特例・片側 isofibration・通常圏の iso commaを照合。任意の試験対象からの Fun の core による categorical pullback の判定。個別の catPullback の表現性は図式を固定する。

:::

:::proposition "kerodon_4_5_3_17"
Kerodon Proposition 4.5.3.17（[Tag 033G](https://kerodon.net/tag/033G)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：厳密 pullback の特例・片側 isofibration・通常圏の iso commaを照合。categorical pullback 正方形を反対 ∞ 圏に移す iff。通常の IsPullback の圏同値による保存は別条件。

:::

:::proposition "kerodon_4_5_3_18"
Kerodon Proposition 4.5.3.18（[Tag 033H](https://kerodon.net/tag/033H)）。対応表の状態：なし。

引用はKan–Quillenの局所化とKan置換模型のIsHomotopyPullbackの対称性。原文の可逆path模型への圏同値との比較がなく、Kanの特殊形でも同じ述語と確認できない。

宣言：`SerrePositivity.KST.Comparison.isHomotopyPullback_flip_iff`、`SerrePositivity.KST.Comparison.IsHomotopyPullback`

:::

:::proposition "kerodon_4_5_3_19" (uses := "kerodon_1_4_0_1, kerodon_3_4_1_11, kerodon_4_5_3_15")
Kerodon Proposition 4.5.3.19（[Tag 033J](https://kerodon.net/tag/033J)）。対応表の状態：なし。

Kan置換模型の局所化によるホモトピーpullbackの貼り合わせは別の述語。原文のcategorical pullbackとの同定がさらに必要。

宣言：`SerrePositivity.KST.Comparison.isHomotopyPullback_paste_horiz`、`SerrePositivity.KST.Fibration.isHomotopyPullback_left_of_horiz`

:::

:::proposition "kerodon_4_5_3_20" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.pullbackMap_isQCatEquivalence_of_components, SerrePositivity.KST.Comparison.isHomotopyPullback_iff_of_localized_isIso") (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_3_4_1_13, kerodon_4_5_1_22, kerodon_4_5_3_15")
Kerodon Proposition 4.5.3.20（[Tag 033K](https://kerodon.net/tag/033K)）。対応表の状態：一部。

pullbackMap\_isQCatEquivalence\_of\_components は両面が指定した厳密pullbackで、左脚がEquivalenceLiftingの場合に、同じ比較射F₀₁=pullback.mapの圏同値性を直接返す。任意のcategorical pullbackの三条件全体は含まない。

:::

:::corollary "kerodon_4_5_3_21" (uses := "kerodon_1_4_0_1")
Kerodon Corollary 4.5.3.21（[Tag 033L](https://kerodon.net/tag/033L)）。対応表の状態：なし。

exists\_catPullbackEquivalence は二つの選んだ模型の間に何らかの圏同値があるという結論。原文の特定の誘導射が同値であるという同じ射の結論ではない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_catPullbackEquivalence_of_strictSpanEquivalence`

:::

:::proposition "kerodon_4_5_3_22" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsQCatEquivalence.pullback_snd_of_relativePath") (uses := "kerodon_1_4_0_1, kerodon_3_4_1_5, kerodon_4_5_1_22, kerodon_4_5_3_15")
Kerodon Proposition 4.5.3.22（[Tag 033M](https://kerodon.net/tag/033M)）。対応表の状態：一部。

pullback\_snd\_of\_relativePath は四角が厳密なpullbackで、もう一方の脚にInnerFibrationと相対pathの自明Kan性を加えた場合、同じF′=pullback.sndの圏同値性を直接返す。任意の四角のcategorical pullbackとのiffは含まない。

:::

:::corollary "kerodon_4_5_3_23" (uses := "kerodon_1_4_0_1, kerodon_4_5_3_1, kerodon_4_5_3_22")
Kerodon Corollary 4.5.3.23（[Tag 0570](https://kerodon.net/tag/0570)）。対応表の状態：なし。

laxPullbackEquivalenceSubcomplexの包含の充満忠実性とcatPullbackとの同型はあるが、原文のδはCからの対角埋め込みで包含とは異なる射。その像との比較がさらに要る。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackEquivalenceSubcomplexIso`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxPullbackEquivalenceSubcomplex_isFullyFaithful`

:::

:::corollary "kerodon_4_5_3_24" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_1_3_2, kerodon_4_5_3_23, kerodon_4_5_4_14")
Kerodon Corollary 4.5.3.24（[Tag 02VM](https://kerodon.net/tag/02VM)）。対応表の状態：なし。

path置換のUのEquivalenceLiftingはKが準圏の追加仮定で得られるが、引用型にはjのMono性・圏同値性・分解式を合わせた結論がない。sectionという構成の材料だけは数えない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.kanEquivalenceLifting_equivalencePathReplacementMap`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementSection`

:::

:::proposition "kerodon_4_5_3_27" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_4_3_19, kerodon_4_4_5_7, kerodon_4_5_1_22, kerodon_4_5_3_15")
Kerodon Proposition 4.5.3.27（[Tag 033P](https://kerodon.net/tag/033P)）。対応表の状態：なし。

Cat∞での厳密pullbackの極限錐という性質は、原文の可逆path模型への特定比較射の同値性とのiffを直接返さない。Kan–Quillenの別模型のiffも同定が必要。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.qCatPullbackInfinityCone_isLimit`、`SerrePositivity.KST.Comparison.isHomotopyPullback_iff_strict_of_left_fibration`

:::

:::corollary "kerodon_4_5_3_28" (uses := "kerodon_1_4_0_1")
Kerodon Corollary 4.5.3.28（[Tag 033R](https://kerodon.net/tag/033R)）。対応表の状態：なし。

qCatPullbackInfinityCone\_isLimit は錐としての極限性。原文のcategorical pullbackの定義の指定比較射の同値性と結ぶ宣言がなく、別の特徴づけへの比較が必要。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.qCatPullbackInfinityCone_isLimit`

:::

:::corollary "kerodon_4_5_3_29" (uses := "kerodon_1_4_0_1, kerodon_4_5_3_28")
Kerodon Corollary 4.5.3.29（[Tag 033T](https://kerodon.net/tag/033T)）。対応表の状態：なし。

exists\_strictPullback\_catPullback\_equivalence は何らかの圏同値の存在。原文の(C₀,C₁)↦(C₀,C₁,id)という特定射が同値という型ではない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_strictPullback_catPullback_equivalence`

:::

:::corollary "kerodon_4_5_3_30" (uses := "kerodon_1_4_0_1, kerodon_4_5_3_19, kerodon_4_5_3_27, kerodon_4_5_3_28")
Kerodon Corollary 4.5.3.30（[Tag 033U](https://kerodon.net/tag/033U)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：厳密 pullback の特例・片側 isofibration・通常圏の iso commaを照合。categorical pullback 正方形での任意の点の二つのファイバーの比較同値。Kan の cospan の比較は設定が異なる。

:::

:::corollary "kerodon_4_5_3_31" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.vertexFiberMap_isQCatEquivalence_of_precompositionEquivalence, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_vertexFiberMap_pre") (uses := "kerodon_1_4_0_1, kerodon_4_5_3_22, kerodon_4_5_3_30")
Kerodon Corollary 4.5.3.31（[Tag 01HK](https://kerodon.net/tag/01HK)）。対応表の状態：一部。

vertexFiberMap\_isQCatEquivalence\_of\_precompositionEquivalence は同じ底上のleft fibrationで、比較fに前合成同値も仮定する場合の同じfiberMapの圏同値性。底のFが恒等である範囲とこの追加仮定に限る。

:::

:::corollary "kerodon_4_5_3_33" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsQCatEquivalence.pullback_snd_isPrecompositionEquivalence_of_kanEquivalenceLifting, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsQCatEquivalence.pullback_snd_of_relativePath")
Kerodon Corollary 4.5.3.33（[Tag 01HJ](https://kerodon.net/tag/01HJ)）。対応表の状態：本体にある。

仮定：∞ 圏間の圏同値 e と EquivalenceLifting を持つ p が同じ標的を持つ（Kerodon と一致）。結論：圏同値側の底変換 pullback.snd e p が前合成同値。両端が ∞ 圏なので圏同値に対応（一致）。

:::

:::corollary "kerodon_4_5_3_34" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isPrecompositionEquivalence_spanPullbackMap_of_equivalenceLifting") (uses := "kerodon_1_4_0_1, kerodon_4_5_3_21, kerodon_4_5_3_29")
Kerodon Corollary 4.5.3.34（[Tag 03PM](https://kerodon.net/tag/03PM)）。対応表の状態：一部。

指定した相対pathの0端点評価の自明Kan性も仮定すると、spanPullbackMapについてIsPrecompositionEquivalenceを直接得る。pullbackの準圏性の下では同じ射の圏同値となる。原文のisofibrationだけから追加仮定を解消していない。

:::

:::corollary "kerodon_4_5_3_35" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.relativeFunctorPre_isQCatEquivalence_of_precompositionEquivalence, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.relativeFunctorOverPre_isQCatEquivalence") (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_4_5_6, kerodon_4_5_3_31, kerodon_4_5_4_8")
Kerodon Corollary 4.5.3.35（[Tag 033V](https://kerodon.net/tag/033V)）。対応表の状態：一部。

relativeFunctorPre/OverPreの二宣言はUがleft fibrationで、fがIsPrecompositionEquivalenceの場合に同じ底上の制限射の圏同値性を直接返す。isofibrationだけ・π₀での原文のcategorical equivalenceだけの場合は含まない。

:::

:::corollary "kerodon_4_5_3_36"
Kerodon Corollary 4.5.3.36（[Tag 02C5](https://kerodon.net/tag/02C5)）。対応表の状態：なし。

relativeFunctorPost は底B上の関手空間の後合成で、原文のA上を固定するFun\_\{A/\}(B,C)とは別の空間。境界制限を保つ比較が必要。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.relativeFunctorPost_isQCatEquivalence_of_precompositionEquivalence`

:::

# 4.5.4 Categorical Equivalence

%%%
number := false
tag := "kerodon-4-5-4"
%%%

Kerodon [Tag 01E7](https://kerodon.net/tag/01E7)

:::definition "kerodon_4_5_4_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence")
Kerodon Definition 4.5.4.1（[Tag 01E8](https://kerodon.net/tag/01E8)）。対応表の状態：一部。

IsPrecompositionEquivalenceは全試験準圏で前合成が圏同値という強い条件。そのcoreの同値をπ₀に送れば原文の同型類の全単射条件を直接満たすが、逆の比較は含まない。

:::

:::proposition "kerodon_4_5_4_4" (lean := "SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsPrecompositionEquivalence.isWeakHomotopyEquivalence") (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1")
Kerodon Remark 4.5.4.4（[Tag 01EB](https://kerodon.net/tag/01EB)）。対応表の状態：一部。

IsPrecompositionEquivalence.isWeakHomotopyEquivalence は同じfの弱ホモトピー同値性を直接返す。原文の試験準圏でのπ₀全単射より強い前合成の圏同値を仮定した場合だけ。

:::

:::proposition "kerodon_4_5_4_8" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isPrecompositionEquivalence_iff_isQCatEquivalence") (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1")
Kerodon Proposition 4.5.4.8（[Tag 01EF](https://kerodon.net/tag/01EF)）。対応表の状態：一部。

IsPrecompositionEquivalenceは原文(3)。各前合成の圏同値をcoreに送りπ₀を取ると(3)⇒(1)の向きを直接得る。原文のπ₀条件からの逆向きは含まない。

:::

:::corollary "kerodon_4_5_4_9" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isPrecompositionEquivalence_iff_of_homotopy, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsQCatEquivalence.ofFunctorIso")
Kerodon Corollary 4.5.4.9（[Tag 033Z](https://kerodon.net/tag/033Z)）。対応表の状態：本体にある。

仮定：∞ 圏を標的とする f,g が自然同型。Lean は点ごとに可逆な prism で代表を取る（Kerodon と一致）。結論：前合成同値の iff。両端が ∞ 圏なら FunctorIso から同値を移す版もある（一致）。

:::

:::corollary "kerodon_4_5_4_10" (uses := "kerodon_1_4_0_1, kerodon_4_5_4_8")
Kerodon Corollary 4.5.4.10（[Tag 023C](https://kerodon.net/tag/023C)）。対応表の状態：なし。

引用は自然変換の成分t.app(∐objs)の前合成同値性。原文の任意の族f\_iの余積射とはそのまま同じ射でなく、関手の余極限比較の同定がさらに要る。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isPrecompositionEquivalence_of_coproduct_colimit`

:::

:::proposition "kerodon_4_5_4_11" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.trivialKanFibration_ihom_map") (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_1_4_6_10, kerodon_4_4_4_4")
Kerodon Proposition 4.5.4.11（[Tag 01EG](https://kerodon.net/tag/01EG)）。対応表の状態：一部。

isQCatEquivalence\_of\_trivialKanFibration は始域・終域も準圏の場合に同じpの圏同値性を直接返す。一般の単体集合上の自明Kan射の主張は含まない。

:::

:::corollary "kerodon_4_5_4_12" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.qCatEquivalenceOfTrivialKanFibration")
Kerodon Corollary 4.5.4.12（[Tag 01EH](https://kerodon.net/tag/01EH)）。対応表の状態：本体にある。

仮定：∞ 圏間の自明 Kan ファイブレーション p（Kerodon と一致）。結論：指定された p が IsQCatEquivalence。逆関手を束ねた版もある（一致）。

:::

:::corollary "kerodon_4_5_4_13" (uses := "kerodon_1_4_0_1, kerodon_4_4_5_10, kerodon_4_5_4_12")
Kerodon Corollary 4.5.4.13（[Tag 02C4](https://kerodon.net/tag/02C4)）。対応表の状態：なし。

引用は端点への射影の自明Kan性とその圏同値性。原文の反対方向のδと恒等辺の切断式・二対三則を組み合わせる議論が型の結論にないため、別の射だけではpartialとしない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.trivialKanFibration_equivalencePathEndpoint_zero`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration`

:::

:::corollary "kerodon_4_5_4_14" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isPrecompositionEquivalence_of_innerAnodyne")
Kerodon Corollary 4.5.4.14（[Tag 01EJ](https://kerodon.net/tag/01EJ)）。対応表の状態：本体にある。

仮定：内アノダインな射 f（Lean が弱い：単射性は内アノダイン性に含む）。結論：f が任意の試験 ∞ 圏に対する前合成同値（Lean が強い：各 π₀ の全単射を含む）。

:::

# 4.5.5 Categorical Pushout Squares

%%%
number := false
tag := "kerodon-4-5-5"
%%%

Kerodon [Tag 01F6](https://kerodon.net/tag/01F6)

:::definition "kerodon_4_5_5_1" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1")
Kerodon Definition 4.5.5.1（[Tag 01F7](https://kerodon.net/tag/01F7)）。対応表の状態：なし。

isPullback\_pre\_of\_isPushout は内部Homの厳密pullback性。原文の全試験準圏のcoreでのホモトピーpullback性の述語や、その比較を直接与えない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isPullback_pre_of_isPushout`

:::

:::proposition "kerodon_4_5_5_4" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_1_5_3_7, kerodon_4_5_3_15")
Kerodon Proposition 4.5.5.4（[Tag 0340](https://kerodon.net/tag/0340)）。対応表の状態：なし。

通常pushoutを内部Homが通常pullbackに送る部品。任意の正方形のcategorical pushoutとcategorical pullbackのいずれの含意も型の結論ではない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isPullback_pre_of_isPushout`

:::

:::corollary "kerodon_4_5_5_5" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_4_5_3, kerodon_4_5_3_30, kerodon_4_5_5_4")
Kerodon Corollary 4.5.5.5（[Tag 02VP](https://kerodon.net/tag/02VP)）。対応表の状態：なし。

引用は底上のrelativeFunctorOverPreの厳密pullbackで、原文の境界を固定したFun\_\{A/\}の圏同値とは対象・射・結論が異なる。

宣言：`SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeFunctorOverPre_isPullback_of_isPushout`

:::

:::proposition "kerodon_4_5_5_6"
Kerodon Proposition 4.5.5.6（[Tag 0344](https://kerodon.net/tag/0344)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：厳密 pushout の特例・単射・アノダイン・双対と通常圏を照合。反対単体集合で categorical pushout 性が同値。op の IsPushout 保存だけではホモトピーの述語を移さない。

:::

:::proposition "kerodon_4_5_5_7"
Kerodon Proposition 4.5.5.7（[Tag 01F9](https://kerodon.net/tag/01F9)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：厳密 pushout の特例・単射・アノダイン・双対と通常圏を照合。categorical pushout の転置不変性。厳密な IsPushout.flip は別の普遍性。

:::

:::proposition "kerodon_4_5_5_8" (uses := "kerodon_1_1_0_6, kerodon_3_4_1_11")
Kerodon Proposition 4.5.5.8（[Tag 01FA](https://kerodon.net/tag/01FA)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：厳密 pushout の特例・単射・アノダイン・双対と通常圏を照合。左の categorical pushout を仮定した横貼り合わせの消去則。厳密な押し出しの貼り合わせでは不足。

:::

:::proposition "kerodon_4_5_5_9" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isPrecompositionEquivalence_of_pushout_gluing") (uses := "kerodon_1_1_0_6, kerodon_3_4_1_13, kerodon_4_5_4_8")
Kerodon Proposition 4.5.5.9（[Tag 01FB](https://kerodon.net/tag/01FB)）。対応表の状態：一部。

isPrecompositionEquivalence\_of\_pushout\_gluing は両面が厳密pushoutで指定脚がMono、三成分がIsPrecompositionEquivalenceの場合に、同じ第4成分dの前合成同値性を直接返す。一般のcategorical pushoutの三条件全部は含まない。

:::

:::proposition "kerodon_4_5_5_10" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence.of_isPushout, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence.of_isPushout_of_mono_other") (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_3_4_1_5, kerodon_4_5_4_8")
Kerodon Proposition 4.5.5.10（[Tag 01FC](https://kerodon.net/tag/01FC)）。対応表の状態：一部。

IsPrecompositionEquivalence.of\_isPushout と of\_isPushout\_of\_mono\_other は四角が厳密pushoutで一方の脚がMonoの場合に、同じf′の前合成同値性を直接返す。原文の任意の四角のiffやπ₀だけの仮定は含まない。

:::

:::proposition "kerodon_4_5_5_11" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_4_5_3, kerodon_4_5_3_27, kerodon_4_5_4_8, kerodon_4_5_5_4")
Kerodon Proposition 4.5.5.11（[Tag 01FF](https://kerodon.net/tag/01FF)）。対応表の状態：なし。

内部Homの厳密pullback性だけは、原文の任意の比較ρがcategorical equivalenceであることとcategorical pushout性とのiffを直接述べない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isPullback_pre_of_isPushout`

:::

:::corollary "kerodon_4_5_5_14" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isPrecompositionEquivalence_of_pushout_gluing")
Kerodon Corollary 4.5.5.14（[Tag 0345](https://kerodon.net/tag/0345)）。対応表の状態：本体にある。

仮定：対応する各射の可換式、両方の押し出しの選択、対応する脚 i,i′ が単射、3 本の比較が圏同値（Kerodon と一致）。結論：誘導された押し出し間の比較が前合成同値（Lean が強い：π₀ 全単射を含む）。

:::

:::corollary "kerodon_4_5_5_15" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence.pushoutObjObj, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence.pushoutObjObj_right") (uses := "kerodon_1_1_0_6, kerodon_4_5_5_10, kerodon_4_5_5_11")
Kerodon Corollary 4.5.5.15（[Tag 01FL](https://kerodon.net/tag/01FL)）。対応表の状態：一部。

pushoutObjObj はiにIsPrecompositionEquivalenceを仮定する場合の同じpushout-productの結論を直接返す。i′側からの引用はi′にもMonoを追加する。π₀だけの原文のcategorical equivalenceとの逆比較は含まない。

:::

# 4.5.6 Isofibrations of Simplicial Sets

%%%
number := false
tag := "kerodon-4-5-6"
%%%

Kerodon [Tag 01FU](https://kerodon.net/tag/01FU)

:::proposition "kerodon_4_5_6_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceLifting_iff_inner_and_invertibleTargetLifting, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceLifting_of_innerFibration_of_targetLifting")
Kerodon Proposition 4.5.6.1（[Tag 01FR](https://kerodon.net/tag/01FR)）。対応表の状態：本体にある。

仮定：∞ 圏間の射 U（Kerodon と一致）。結論：EquivalenceLifting と、内ファイブレーションかつ指定終点の可逆辺を持ち上げる条件が同値（一致）。

:::

:::lemma_ "kerodon_4_5_6_2" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence.trivialKanFibration_pre")
Kerodon Lemma 4.5.6.2（[Tag 01FS](https://kerodon.net/tag/01FS)）。対応表の状態：本体にある。

仮定：Quasicategory X と単射な前合成同値 i:A→B（Kerodon と一致）。結論：制限が自明 Kan ファイブレーション（Lean が強い：頂点全射として任意の f₀:A→X の延長を含む）。

:::

:::lemma_ "kerodon_4_5_6_3" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.exists_kanPrism_extension_of_precompositionEquivalence")
Kerodon Lemma 4.5.6.3（[Tag 01FT](https://kerodon.net/tag/01FT)）。対応表の状態：一部。

exists\_kanPrism\_extension\_of\_precompositionEquivalence はiに強い前合成同値を仮定すると同じ二端点とA上の制限を持つ延長の存在を直接返す。可逆なu₀なら全延長が可逆という後半は含まない。

:::

:::proposition "kerodon_4_5_6_4" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isPrecompositionEquivalence_iff_llp_boundaryTests, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting") (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_4_5_5, kerodon_4_5_6_1")
Kerodon Proposition 4.5.6.4（[Tag 02R2](https://kerodon.net/tag/02R2)）。対応表の状態：一部。

EquivalenceLiftingの定義は単射かつIsPrecompositionEquivalenceのiに対するHasLiftingPropertyそのもの。isofibrationとの二条件のiffを通じて原文の持ち上げ条件を直接得るが、π₀だけの仮定や逆向きは含まない。

:::

:::definition "kerodon_4_5_6_5" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting")
Kerodon Definition 4.5.6.5（[Tag 01FV](https://kerodon.net/tag/01FV)）。対応表の状態：本体にある。

仮定：任意の単体集合の射 q（Kerodon と一致）。結論：EquivalenceLifting は単射な前合成同値に対する右持ち上げ性（一致）。

:::

:::proposition "kerodon_4_5_6_14" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting.relativeInternalHom")
Kerodon Proposition 4.5.6.14（[Tag 01G3](https://kerodon.net/tag/01G3)）。対応表の状態：本体にある。

仮定：単体集合間の EquivalenceLifting を持つ q、単射 i、内部 Hom の引き戻しの選択（Kerodon と一致）。結論：制限と後合成の比較射 π が EquivalenceLifting（一致）。

:::

:::corollary "kerodon_4_5_6_15" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting.internalHom")
Kerodon Corollary 4.5.6.15（[Tag 01G4](https://kerodon.net/tag/01G4)）。対応表の状態：本体にある。

仮定：単体集合間の EquivalenceLifting を持つ q と任意の K（Kerodon と一致）。結論：(ihom K).map q が EquivalenceLifting（一致）。

:::

:::corollary "kerodon_4_5_6_16" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.kanEquivalenceLifting_relativeFunctorOverPre_of_cocartesian, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting.relativeInternalHom")
Kerodon Corollary 4.5.6.16（[Tag 02VQ](https://kerodon.net/tag/02VQ)）。対応表の状態：一部。

kanEquivalenceLifting\_relativeFunctorOverPre\_of\_cocartesian はqをcocartesian fibrationに強めた場合の、同じ底上の制限射のEquivalenceLiftingを直接返す。一般isofibrationでは相対内部Homのfiberとの同定が必要。

:::

:::proposition "kerodon_4_5_6_18" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence.trivialKanFibration_relative_pre, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.relativeFunctorPre_trivialKanFibration_of_precompositionEquivalence") (uses := "kerodon_1_1_0_6, kerodon_4_5_5_15")
Kerodon Proposition 4.5.6.18（[Tag 01G5](https://kerodon.net/tag/01G5)）。対応表の状態：一部。

trivialKanFibration\_relative\_pre はqが単射jによる前合成射である場合の同じ相対指数比較の自明Kan性を直接返す。iにも原文より強いIsPrecompositionEquivalenceを仮定する。一般qは含まない。

:::

:::corollary "kerodon_4_5_6_19" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence.trivialKanFibration_pre")
Kerodon Corollary 4.5.6.19（[Tag 01G6](https://kerodon.net/tag/01G6)）。対応表の状態：本体にある。

仮定：Quasicategory X と単射な前合成同値 i:A→B（Kerodon と一致）。結論：制限 Fun(B,X)→Fun(A,X) が自明 Kan ファイブレーション（一致）。

:::

:::proposition "kerodon_4_5_6_20" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsQCatEquivalence.trivialKanFibration_of_kanEquivalenceLifting, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration") (uses := "kerodon_1_1_0_6, kerodon_4_5_4_11")
Kerodon Proposition 4.5.6.20（[Tag 01G7](https://kerodon.net/tag/01G7)）。対応表の状態：一部。

準圏間で圏同値をIsQCatEquivalenceとして与えた場合、trivialKanFibration\_of\_kanEquivalenceLifting と逆の自明Kan射の同値性が同じqの二方向を返す。任意単体集合の原文のπ₀による定義の範囲は含まない。

:::

# 4.5.7 Isofibrant Diagrams

%%%
number := false
tag := "kerodon-4-5-7"
%%%

Kerodon [Tag 0346](https://kerodon.net/tag/0346)

:::definition "kerodon_4_5_7_1" (uses := "kerodon_1_1_0_6")
Kerodon Definition 4.5.7.1（[Tag 0347](https://kerodon.net/tag/0347)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：一次元・通常圏・各段の比較・点wise の同値を照合。自然変換の全成分が圏同値という SSet 値図式の述語。equivalenceDiagrams は特定の関手の比較。

:::

:::definition "kerodon_4_5_7_3"
Kerodon Definition 4.5.7.3（[Tag 0349](https://kerodon.net/tag/0349)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：一次元・通常圏・各段の比較・点wise の同値を照合。単射かつ点ごとの圏同値に対する図式全体の延長条件。Reedy の Kan ファイブレーション版は別の弱同値。

:::

:::proposition "kerodon_4_5_7_6"
Kerodon Proposition 4.5.7.6（[Tag 034D](https://kerodon.net/tag/034D)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：一次元・通常圏・各段の比較・点wise の同値を照合。整礎半順序上の図式の matching map の isofibration 判定。Reedy モデルの matching fibration はモデル圏構造に依存。

:::

:::definition "kerodon_4_5_7_10"
Kerodon Variant 4.5.7.10（[Tag 0572](https://kerodon.net/tag/0572)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：一次元・通常圏・各段の比較・点wise の同値を照合。Kan 複体の弱余骨格の塔の isofibrant 性と通常の余骨格塔の反例。IsCoskeletal は単体集合一つの条件。

:::

:::proposition "kerodon_4_5_7_11" (lean := "SerrePositivity.KST.Spectra.ReedyWeightRestrictionFibration.fibration, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre_cospan_trivialKanFibration") (uses := "kerodon_1_1_0_6, kerodon_4_5_5_15")
Kerodon Proposition 4.5.7.11（[Tag 034H](https://kerodon.net/tag/034H)）。対応表の状態：一部。

Reedy Kan fibrantな余単体図式とReedy単射な重みの場合、fibrationは同じweightedSectionsPreのKan fibration性を直接返す。Kan空間のisofibrationという範囲に限り、一般のisofibrant図式とlevelwise categorical equivalence時の後半は含まない。

:::

:::corollary "kerodon_4_5_7_12" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.weightedSections_tower_kanComplex") (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_5_7_11")
Kerodon Corollary 4.5.7.12（[Tag 034K](https://kerodon.net/tag/034K)）。対応表の状態：一部。

添字圏をAsSmall ℕop、零段Kan・隣接遷移fibrationの塔に制限すると、weightedSections\_tower\_kanComplexは同じ豊穣HomのKan性を直接与え、従って準圏になる。任意の小圏上のisofibrant図式全体ではない。

:::

:::corollary "kerodon_4_5_7_13" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.quasicategory_of_discrete_limit, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.quasicategory_of_inverseSequence_limit") (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_5_7_12")
Kerodon Corollary 4.5.7.13（[Tag 034L](https://kerodon.net/tag/034L)）。対応表の状態：一部。

quasicategory\_of\_discrete\_limit と quasicategory\_of\_inverseSequence\_limit は離散図式および内ファイブレーションの可算逆列の厳密極限に同じ準圏性を直接返す。任意小圏のisofibrant図式は含まない。

:::

:::proposition "kerodon_4_5_7_14" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.weightedSections_tower_kanComplex, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre_tower_trivialKanFibration")
Kerodon Proposition 4.5.7.14（[Tag 034M](https://kerodon.net/tag/034M)）。対応表の状態：一部。

添字をAsSmall ℕopの塔、標的を零段Kan・隣接遷移fibrationに制限し、原文のlevelwise categorical equivalenceに加えて重みの各成分のanodyne性を仮定すると、同じweightedSectionsPreがtrivial Kan fibration（従って圏同値）。anodyneだけから原文のlevelwise圏同値を主張しない。

:::

:::corollary "kerodon_4_5_7_15"
Kerodon Corollary 4.5.7.15（[Tag 034N](https://kerodon.net/tag/034N)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：一次元・通常圏・各段の比較・点wise の同値を照合。isofibrant 図式の点ごとの圏同値に対する豊穣逆の構成。点ごとの通常の自然同型は強い仮定。

:::

:::corollary "kerodon_4_5_7_16" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1")
Kerodon Corollary 4.5.7.16（[Tag 034P](https://kerodon.net/tag/034P)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：一次元・通常圏・各段の比較・点wise の同値を照合。標的の点ごとの圏同値に対する豊穣 Hom の後合成同値。標的図式の isofibrant 性で述べる型がない。

:::

:::corollary "kerodon_4_5_7_17" (uses := "kerodon_1_4_0_1, kerodon_4_5_7_16")
Kerodon Corollary 4.5.7.17（[Tag 034Q](https://kerodon.net/tag/034Q)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：一次元・通常圏・各段の比較・点wise の同値を照合。isofibrant な二図式の点ごとの圏同値が極限の圏同値を誘導。Kan 型の特殊な図式の比較では仮定が異なる。

:::

:::corollary "kerodon_4_5_7_19"
Kerodon Corollary 4.5.7.19（[Tag 069F](https://kerodon.net/tag/069F)）。対応表の状態：なし。

limit\_kanComplex は厳密極限のKan性だけで、原文のshiftと対角を使う指定四角のcategorical pullback性を述べない。極限のKan性はその結論の成分ではない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.limit_kanComplex`

:::

:::proposition "kerodon_4_5_7_20" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections_cospan_kanComplex, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.weightedSections_tower_kanComplex, SerrePositivity.KST.Spectra.WeightedEndReedyKan.kanComplex") (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_4_4_2_1, kerodon_4_5_7_12, kerodon_4_5_7_16")
Kerodon Proposition 4.5.7.20（[Tag 034S](https://kerodon.net/tag/034S)）。対応表の状態：一部。

weightedSectionsの三つのKan性の宣言はcospan・可算塔・Reedy fibrant余単体図式について原文と同じHom(E,F)のKan性を直接返す。重みや遷移射にも明記された仮定があり、任意小圏は含まない。

:::

:::corollary "kerodon_4_5_7_21" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.limit_kanComplex") (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_4_5_7_20")
Kerodon Corollary 4.5.7.21（[Tag 034T](https://kerodon.net/tag/034T)）。対応表の状態：一部。

limit\_kanComplex はKan fibrationの可算塔で初項がKanのときの同じ厳密極限のKan性。任意小圏の図式の結論は含まない。

:::

:::corollary "kerodon_4_5_7_22" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_4_4_3_6, kerodon_4_4_3_18, kerodon_4_5_7_21")
Kerodon Corollary 4.5.7.22（[Tag 034U](https://kerodon.net/tag/034U)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：一次元・通常圏・各段の比較・点wise の同値を照合。isofibrant 図式で極限と core を交換する同型。relativized core の個別包含の定義だけでは極限を同定しない。

:::

:::corollary "kerodon_4_5_7_23" (uses := "kerodon_1_4_0_1, kerodon_4_5_7_13, kerodon_4_5_7_22")
Kerodon Corollary 4.5.7.23（[Tag 0238](https://kerodon.net/tag/0238)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：一次元・通常圏・各段の比較・点wise の同値を照合。isofibration の塔で core と逆極限を交換し可逆性を各段で判定。core の二脚の引き戻し補題は塔を扱わない。

:::

:::proposition "kerodon_4_5_7_24"
Kerodon Proposition 4.5.7.24（[Tag 05HY](https://kerodon.net/tag/05HY)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：一次元・通常圏・各段の比較・点wise の同値を照合。単体図式で面写像による matching object に対する isofibration 判定。通常の matching object の構成だけでは足りない。

:::

# 4.5.8 Relative Exponentiation

%%%
number := false
tag := "kerodon-4-5-8"
%%%

Kerodon [Tag 02TM](https://kerodon.net/tag/02TM)

:::definition "kerodon_4_5_8_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHom, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomProjection, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseFunctor, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseFunctorValue")
Kerodon Construction 4.5.8.1（[Tag 046N](https://kerodon.net/tag/046N)）。対応表の状態：本体にある。

仮定：任意の単体集合の射 p:K→C と単体集合 D（Kerodon と一致）。結論：fiberwiseHom p D の各単体は底の単体と、その単体に沿う K の引き戻しから D への射。制限は引き戻しの変数変換による。射影は底の単体を取り、標準単体上の評価は fiberwiseFunctorValue に対応（一致）。

:::

:::proposition "kerodon_4_5_8_5" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomEquiv")
Kerodon Proposition 4.5.8.5（[Tag 02TP](https://kerodon.net/tag/02TP)）。対応表の状態：本体にある。

仮定：任意の単体集合の射 p:K→C と底への写像 a:A→C、任意の D（Kerodon と一致）。結論：fiberwiseHomEquiv の逆向きは、底を厳密に保つ A→fiberwiseHom p D を pullback a p 上で評価し、D への射との全単射を与える（一致）。

:::

:::definition "kerodon_4_5_8_10" (uses := "kerodon_1_1_0_6")
Kerodon Definition 4.5.8.10（[Tag 02TX](https://kerodon.net/tag/02TX)）。対応表の状態：なし。

fiberwiseHomProjection\_innerFibration\_iff は内ホーン上の延長と指数のinner性の特徴づけ。原文の任意の基底変換でcategorical equivalenceを保つという定義ではなく、別の判定を結ぶ比較が必要。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.fiberwiseHomProjection_innerFibration_iff`

:::

:::proposition "kerodon_4_5_8_18" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.fiberwiseHomProjection_innerFibration_of_hornEquivalences, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.fiberwiseHomPostcomp_innerFibration") (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_4_5_6_4, kerodon_4_5_8_5, kerodon_4_5_8_10")
Kerodon Proposition 4.5.8.18（[Tag 046Q](https://kerodon.net/tag/046Q)）。対応表の状態：一部。

fiberwiseHomPostcomp\_innerFibration はUがcocartesianでVがEquivalenceLiftingの場合、同じ相対指数の後合成射のinner fibration性を直接返す。原文のisofibrationのinner性成分のみで、追加仮定と可逆辺持ち上げの不足がある。

:::

:::corollary "kerodon_4_5_8_19" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.fiberwiseHomProjection_innerFibration_of_hornEquivalences") (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_5_8_18")
Kerodon Corollary 4.5.8.19（[Tag 02U8](https://kerodon.net/tag/02U8)）。対応表の状態：一部。

fiberwiseHomProjection\_innerFibration\_of\_hornEquivalences は内ホーンの逆像射にIsPrecompositionEquivalenceも仮定すると、同じ指数射影のinner fibration性を直接返す。原文のisofibrationのこの成分だけで、exponentiableだけの仮定との比較は含まない。

:::

