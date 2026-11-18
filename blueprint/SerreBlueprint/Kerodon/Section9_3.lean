import Verso
import VersoManual
import VersoBlueprint
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.CategoryTheory.Limits.Preserves.Finite

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "9.3 Ind-Completions of ∞-Categories" =>
%%%
number := false
tag := "kerodon-9-3"
%%%

Kerodon の 9.3 節（[Tag 06FR](https://kerodon.net/tag/06FR)）の項目と、SerrePositivity・Mathlib の宣言との対応。本文は対応表（research/kerodon-coverage）の判定の理由の要約で、Kerodon の本文の写しではない。

# 9.3.1 Ind-Completion

%%%
number := false
tag := "kerodon-9-3-1"
%%%

Kerodon [Tag 063J](https://kerodon.net/tag/063J)

:::definition "kerodon_9_3_1_1"
Kerodon Definition 9.3.1.1（[Tag 063K](https://kerodon.net/tag/063K)）。対応表の状態：一部。

B6型照合：「Ind 完備化を与える」述語はなし。具体的な模型 IndInfinity ℵ0 C（C 小）とその性質（compact 生成・普遍性）。Mathlib の Ind C は 1 圏。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda_isKappaCompactGenerating`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indKappaContinuousRestrictionEquivalence`

:::

:::definition "kerodon_9_3_1_2"
Kerodon Notation 9.3.1.2（[Tag 063L](https://kerodon.net/tag/063L)）。対応表の状態：一部。

小さい準圏Cの標準IndInfinityとindYonedaの充満忠実性・filtered余極限存在・普遍性は原文の同じCに対するInd完備化の存在成分を直接実現する。一意性と関手性の全体は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda_isFullyFaithful`

:::

:::definition "kerodon_9_3_1_3"
Kerodon Variant 9.3.1.3（[Tag 063M](https://kerodon.net/tag/063M)）。対応表の状態：なし。

Indの制限同値は原文の指定Pro完備化と反転同値を構成しない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indKappaContinuousRestrictionEquivalence`

:::

:::definition "kerodon_9_3_1_4"
Kerodon Definition 9.3.1.4（[Tag 063N](https://kerodon.net/tag/063N)）。対応表の状態：一部。

B6型照合：9.3.1.1 と同じ：述語はなく κ の模型 IndInfinity κ C とその性質。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda_isKappaCompactGenerating`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indKappaContinuousRestrictionEquivalence`

:::

:::definition "kerodon_9_3_1_5"
Kerodon Notation 9.3.1.5（[Tag 063P](https://kerodon.net/tag/063P)）。対応表の状態：一部。

小さい準圏Cの標準IndInfinityとindYonedaの充満忠実性・filtered余極限存在・普遍性は原文の同じCに対するInd完備化の存在成分を直接実現する。一意性と関手性の全体は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity`

:::

:::definition "kerodon_9_3_1_7" (uses := "kerodon_1_4_0_1, kerodon_9_2_1_3, kerodon_9_2_2_6")
Kerodon Variant 9.3.1.7（[Tag 063R](https://kerodon.net/tag/063R)）。対応表の状態：なし。

IndInfinityの宇宙小κ-filtered閉包は原文の指定λ-smallだけの完備化ではない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity`

:::

:::definition "kerodon_9_3_1_8"
Kerodon Notation 9.3.1.8（[Tag 063S](https://kerodon.net/tag/063S)）。対応表の状態：なし。

同じく数値λのIndκλ完備化の存在と一意性を返す型ではない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity`

:::

:::definition "kerodon_9_3_1_12" (uses := "kerodon_1_4_0_1")
Kerodon Definition 9.3.1.12（[Tag 063X](https://kerodon.net/tag/063X)）。対応表の状態：一部。

B6型照合：Ind 延長という名前の述語はない。κ-連続な左 Kan 延長の存在と制限の同値で代用。λ=∞（Ind\_κ）の場合だけ。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.ind_exists_leftKanExtension`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indLeftKanExtension_preservesSmallKappaFilteredColimits`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indKappaContinuousRestrictionEquivalence`

:::

:::definition "kerodon_9_3_1_13"
Kerodon Notation 9.3.1.13（[Tag 06N2](https://kerodon.net/tag/06N2)）。対応表の状態：一部。

B6型照合：名前の付いた Ind(F) はない。F ≫ indYoneda に exists\_indComparison を当てれば得られる。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.exists_indComparison`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.ind_exists_leftKanExtension`

:::

:::proposition "kerodon_9_3_1_16"
Kerodon Proposition 9.3.1.16（[Tag 06N3](https://kerodon.net/tag/06N3)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：一つの Ind-Yoneda の局所添字の射影が右ファイブレーションで、左 Kan 延長には κ-filtered 余極限保存がある。任意の U:E→C を同じ二濃度の Ind 完備化の間の右ファイブレーションへ延長する指定引き戻しは見つからない。

:::

# 9.3.2 Recognition of Ind-Completions

%%%
number := false
tag := "kerodon-9-3-2"
%%%

Kerodon [Tag 0650](https://kerodon.net/tag/0650)

:::proposition "kerodon_9_3_2_1" (uses := "kerodon_1_4_0_1")
Kerodon Proposition 9.3.2.1（[Tag 0651](https://kerodon.net/tag/0651)）。対応表の状態：一部。

B6型照合：充満忠実・像 compact ⇒ 延長が充満忠実。λ=∞（Ind\_κ）の場合だけ、C は小さい（宇宙 u）場合。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indComparison_isFullyFaithful_of_compact`

:::

:::corollary "kerodon_9_3_2_2"
Kerodon Corollary 9.3.2.2（[Tag 0652](https://kerodon.net/tag/0652)）。対応表の状態：一部。

B6型照合：Ind(F) の充満忠実性の明示的な宣言はなし。CFF から導ける形。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indComparison_isFullyFaithful_of_compact`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda_isFullyFaithful`

:::

:::proposition "kerodon_9_3_2_3" (uses := "kerodon_1_4_0_1, kerodon_9_3_2_1")
Kerodon Proposition 9.3.2.3（[Tag 0653](https://kerodon.net/tag/0653)）。対応表の状態：一部。

B6型照合：Ind 完備化の判定。「もし」の向き（compact 生成 ⇒ Ind 同値）と模型の性質。λ=∞（Ind\_κ）の場合だけ、C は小さい（宇宙 u）場合。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indComparisonEquivalence`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda_isKappaCompactGenerating`

:::

:::lemma_ "kerodon_9_3_2_5" (uses := "kerodon_1_4_0_1")
Kerodon Lemma 9.3.2.5（[Tag 067F](https://kerodon.net/tag/067F)）。対応表の状態：一部。

B6型照合：compact な余極限頂点は filtered 図式の項の retract。生成の閉包一般ではなく単一の κ-filtered 表示がある場合。λ=∞（Ind\_κ）の場合だけ。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IsKappaCompact.retract_of_colimit`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indCompact_retract_yoneda`

:::

:::proposition "kerodon_9_3_2_6"
Kerodon Proposition 9.3.2.6（[Tag 067G](https://kerodon.net/tag/067G)）。対応表の状態：一部。

B6型照合：Ind\_κ(C) の κ-compact 部分 ≃ Idem(C)（冪等完備化）。模型について、λ=∞（Ind\_κ）の場合だけ。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.compactIndYoneda_isIdempotentCompletion`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.compactIndEquivalence`

:::

:::corollary "kerodon_9_3_2_8"
Kerodon Corollary 9.3.2.8（[Tag 067J](https://kerodon.net/tag/067J)）。対応表の状態：一部。

B6型照合：冪等完備な C ≃ Ind\_κ(C) の κ-compact 部分。λ=∞（Ind\_κ）の場合だけ。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.compactGenerationEquivalence`

:::

:::corollary "kerodon_9_3_2_9"
Kerodon Corollary 9.3.2.9（[Tag 0655](https://kerodon.net/tag/0655)）。対応表の状態：一部。

小さいCの標準Indとcompact生成表示についてindComparison\_isFullyFaithful\_of\_compactは同じ拡張関手の充満忠実性を直接与える。任意のfの全四条件のiffは含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indComparisonEquivalence`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.exists_indComparison`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda_isKappaCompactGenerating`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indComparison_isFullyFaithful_of_compact`

:::

:::corollary "kerodon_9_3_2_10"
Kerodon Corollary 9.3.2.10（[Tag 0656](https://kerodon.net/tag/0656)）。対応表の状態：一部。

小さいCの標準Indとcompact生成表示についてindComparison\_isFullyFaithful\_of\_compactは同じ拡張関手の充満忠実性を直接与える。任意のfの全四条件のiffは含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indComparisonEquivalence`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.exists_indComparison`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda_isKappaCompactGenerating`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indComparison_isFullyFaithful_of_compact`

:::

:::definition "kerodon_9_3_2_13"
Kerodon Variant 9.3.2.13（[Tag 0659](https://kerodon.net/tag/0659)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：有限表示加群から平坦加群への射が有限階数自由加群を経由する型と、加群の忘却による filtered 余極限保存はある。平坦加群自体の有限自由加群による filtered 余極限表示と、その全体の Ind 同値は見つからない。

:::

:::proposition "kerodon_9_3_2_17"
Kerodon Proposition 9.3.2.17（[Tag 065D](https://kerodon.net/tag/065D)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Ind-Yoneda は元の写像空間を比較する充満忠実な包含で、空間の 0-truncated 述語もある。一般の整数 n について (κ,λ) の Ind 全体の局所 n-truncation を元の C と比較する iff は見つからない。

:::

:::corollary "kerodon_9_3_2_18"
Kerodon Corollary 9.3.2.18（[Tag 065E](https://kerodon.net/tag/065E)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：準圏の IndInfinity と通常圏の Ind はそれぞれある。一般の通常圏 C の nerve に対し、前者を通常圏の Ind の nerve と同定する型は見つからない。

:::

:::proposition "kerodon_9_3_2_20"
Kerodon Proposition 9.3.2.20（[Tag 06FT](https://kerodon.net/tag/06FT)）。対応表の状態：なし。

spaceCompactGeneratorInclusionは指定された有限generator像であり、原文の全essentially finite空間の全部分圏との同一視を引用に含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.space_isKappaAccessible_aleph0`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.spaceCompactGeneratorInclusion_isCompactGenerating`

:::

:::definition "kerodon_9_3_2_21"
Kerodon Variant 9.3.2.21（[Tag 06FU](https://kerodon.net/tag/06FU)）。対応表の状態：なし。

宇宙パラメータのInd・空間・unstraighteningの型は、原文の指定数値κ・λ・μの値圏と同じ余極限・小性条件へ比較されていない。固定宇宙の空間の κ-small Kan 対象は非可算正則 κ で κ-compact であり、一般の compact 生成表示から Ind 比較の充満忠実性や同値を得られる。二つの濃度で切った空間部分圏の指定包含と sharply below による同値は見つからない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indComparison_isFullyFaithful_of_compact`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indComparisonEquivalence`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.smallKanObject_isKappaCompact`

:::

:::corollary "kerodon_9_3_2_22"
Kerodon Corollary 9.3.2.22（[Tag 0684](https://kerodon.net/tag/0684)）。対応表の状態：なし。

宇宙パラメータのInd・空間・unstraighteningの型は、原文の指定数値κ・λ・μの値圏と同じ余極限・小性条件へ比較されていない。空間圏の ℵ₀-accessibility と非可算正則 κ で κ-small な Kan 対象の κ-compact 性はある。任意の非可算正則 κ に対して S\_\{\<κ\} の指定包含が空間圏全体の Indκ 完備化となる型は見つからない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.space_isKappaAccessible_aleph0`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.smallKanObject_isKappaCompact`

:::

:::proposition "kerodon_9_3_2_24"
Kerodon Proposition 9.3.2.24（[Tag 06FV](https://kerodon.net/tag/06FV)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：有限単体集合の Kan 置換を生成族とする空間圏の表示と、任意の指定 compact 生成圏に対する Ind 比較はある。本質的有限な準圏の部分から QC 全体を Ind で得る型は見つからない。

:::

:::definition "kerodon_9_3_2_25"
Kerodon Variant 9.3.2.25（[Tag 06FW](https://kerodon.net/tag/06FW)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：小さい生成準圏と単一 κ の Ind の制限同値はある。QC\_\{\<κ\} の包含から QC\_\{\<λ\} への充満忠実性と sharply below の場合の同値は見つからない。

:::

:::corollary "kerodon_9_3_2_26"
Kerodon Corollary 9.3.2.26（[Tag 068T](https://kerodon.net/tag/068T)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：固定宇宙の CatInfinity は準圏で、別途任意の小さい準圏の IndInfinity は構成される。濃度 κ の QC を生成対象に取ったとき全 QC と同定する型は見つからない。

:::

# 9.3.3 Functoriality of Ind-Completion

%%%
number := false
tag := "kerodon-9-3-3"
%%%

Kerodon [Tag 06FX](https://kerodon.net/tag/06FX)

:::proposition "kerodon_9_3_3_1"
Kerodon Proposition 9.3.3.1（[Tag 06FY](https://kerodon.net/tag/06FY)）。対応表の状態：なし。

宇宙パラメータのInd・空間・unstraighteningの型は、原文の指定数値κ・λ・μの値圏と同じ余極限・小性条件へ比較されていない。μ-small の一般形はない。小さい C で Ind の固定頂点写像が小さい（宇宙の意味の局所小）。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.ind_hasSmallFixedVertexMaps`

:::

:::corollary "kerodon_9_3_3_2"
Kerodon Corollary 9.3.3.2（[Tag 06FZ](https://kerodon.net/tag/06FZ)）。対応表の状態：一部。

Cを宇宙で小さく標準Indℵ0に限るとind\_hasSmallFixedVertexMapsは同じIndの写像の局所小性を直接返す。一般の大きい局所小Cは含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.ind_hasSmallFixedVertexMaps`、`CategoryTheory.instLocallySmallFullSubcategoryFunctorOppositeTypeIsIndObject`

:::

:::definition "kerodon_9_3_3_3"
Kerodon Variant 9.3.3.3（[Tag 063W](https://kerodon.net/tag/063W)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：IndInfinity は固定宇宙の前層の充満部分複体。左ファイブレーションのファイバーの本質的小性とは別に、Ind 全体の本質的 μ-small 性を与える濃度評価は見つからない。

:::

:::definition "kerodon_9_3_3_5"
Kerodon Definition 9.3.3.5（[Tag 0640](https://kerodon.net/tag/0640)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：個別の準圏上の Ind の普遍性と延長の保存はある。QC\_\{\<μ\} の自己関手に自然単位を指定し、全対象の二濃度の完備化と全辺の相対 finitary 性を要求する定義は見つからない。

:::

:::proposition "kerodon_9_3_3_7"
Kerodon Proposition 9.3.3.7（[Tag 0642](https://kerodon.net/tag/0642)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：対象ごとの IndInfinity と、その関手制限の普遍同値がある。濃度制限された QC 上で Ind\_\{κ\}\^\{λ\} が一つの関手となる存在と自然同型までの一意性は見つからない。

:::

:::definition "kerodon_9_3_3_8"
Kerodon Notation 9.3.3.8（[Tag 0643](https://kerodon.net/tag/0643)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：指定関手から Ind の左 Kan 拡張を構成する型はある。κ,λ を固定した QC 上の一意な完備化関手と、その F に対する作用を同時に与える型は見つからない。

:::

:::proposition "kerodon_9_3_3_12"
Kerodon Proposition 9.3.3.12（[Tag 0648](https://kerodon.net/tag/0648)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：固定 C の Ind から前層への包含は κ-filtered 余極限を保ち、濃度変更の条件もある。Ind が C を変数とする QC\_\{\<μ\} の関手として μ-small λ-filtered 余極限を保つ型は見つからない。

:::

:::definition "kerodon_9_3_3_13"
Kerodon Definition 9.3.3.13（[Tag 06G1](https://kerodon.net/tag/06G1)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：一つの準圏の Ind 制限同値と、Ind-Yoneda の局所添字への射影の右ファイブレーション性はある。C 上の二つの内ファイブレーションで、全 Δⁿ への基底変更後に (κ,λ) の完備化を要求する定義は見つからない。

:::

:::proposition "kerodon_9_3_3_15"
Kerodon Proposition 9.3.3.15（[Tag 06G3](https://kerodon.net/tag/06G3)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：一点の底に当たる通常の Ind の制限同値はある。一般の内ファイブレーションで二濃度余完備性、各ファイバーの完備化、各辺上の compact 性をまとめた iff は見つからない。

:::

:::corollary "kerodon_9_3_3_17"
Kerodon Corollary 9.3.3.17（[Tag 06G5](https://kerodon.net/tag/06G5)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：単一準圏の IndInfinity とその小 κ-filtered 余完備性を確認した。与えた U の底を保つ二濃度相対完備化と、その構造射の inner fibration 性の存在は見つからない。

:::

:::corollary "kerodon_9_3_3_18"
Kerodon Corollary 9.3.3.18（[Tag 06G6](https://kerodon.net/tag/06G6)）。対応表の状態：なし。

絶対Indの全関手準圏の制限同値は、原文の底上のsection準圏とfiberwise finitary部分圏の同じ制限への比較を含まない。底を点に限る比較も引用で未確認。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indKappaContinuousRestrictionEquivalence`

:::

:::corollary "kerodon_9_3_3_19"
Kerodon Corollary 9.3.3.19（[Tag 06G7](https://kerodon.net/tag/06G7)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：単独の準圏での Ind 延長と cocartesian fibration の述語はある。相対完備化した射影が cocartesian になる主張と、輸送への二濃度 Ind の適用の比較は見つからない。

:::

:::corollary "kerodon_9_3_3_20"
Kerodon Corollary 9.3.3.20（[Tag 06G8](https://kerodon.net/tag/06G8)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：対象ごとの Ind と関手延長はある。本文の輸送表現の四角形で、同じ底 C 上の相対完備化との自然同型を返す型は見つからない。

:::

# 9.3.4 Flat Functors

%%%
number := false
tag := "kerodon-9-3-4"
%%%

Kerodon [Tag 065H](https://kerodon.net/tag/065H)

:::definition "kerodon_9_3_4_1"
Kerodon Definition 9.3.4.1（[Tag 065J](https://kerodon.net/tag/065J)）。対応表の状態：なし。

HasKappaFilteredElementsはpresheafのright unstraightening全体のfiltered性。原文は共変のcategory of elementsのcofiltered性で、反転した同じ積分との比較を引用に持たない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.HasKappaFilteredElements`

:::

:::proposition "kerodon_9_3_4_5"
Kerodon Proposition 9.3.4.5（[Tag 065N](https://kerodon.net/tag/065N)）。対応表の状態：なし。

HasKappaFilteredElementsはright unstraighteningのfiltered条件。原文の共変積分のcofiltered条件への反転比較を含まず、IsIndVertexのiffだけを同じflat性の主張としない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.isIndVertex_iff_hasKappaFilteredElements`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indKappaContinuousRestrictionEquivalence`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda_isKappaCompactGenerating`

:::

:::definition "kerodon_9_3_4_7" (uses := "kerodon_1_4_0_1, kerodon_9_1_1_4")
Kerodon Definition 9.3.4.7（[Tag 065Q](https://kerodon.net/tag/065Q)）。対応表の状態：なし。

HasKappaFilteredElementsはright unstraighteningのfiltered条件。原文の共変積分のcofiltered条件への反転比較と指定数値λ値圏への大きさの比較を含まず、IsIndVertexのiffだけを同じflat性の主張としない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.HasKappaFilteredElements`

:::

:::theorem "kerodon_9_3_4_14" (uses := "kerodon_1_4_0_1, kerodon_8_4_6_8, kerodon_9_3_1_7, kerodon_9_3_4_20, kerodon_9_3_4_21")
Kerodon Theorem 9.3.4.14（[Tag 065X](https://kerodon.net/tag/065X)）。対応表の状態：なし。

HasKappaFilteredElementsはright unstraighteningのfiltered条件。原文の共変積分のcofiltered条件への反転比較と指定数値λ値圏への大きさの比較を含まず、IsIndVertexのiffだけを同じflat性の主張としない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.isIndVertex_iff_hasKappaFilteredElements`

:::

:::corollary "kerodon_9_3_4_15" (uses := "kerodon_1_4_0_1, kerodon_4_9_8_12, kerodon_8_4_2_4, kerodon_8_4_2_7, kerodon_9_3_4_14")
Kerodon Corollary 9.3.4.15（[Tag 06GA](https://kerodon.net/tag/06GA)）。対応表の状態：なし。

elementsから標準commaへの同値と密度余錐はあるが、原文の指定λ-small性と元の全comma形状でのκ-filtered性を移す同じ比較を引用に含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indElementsLeftKanComparison_isQCatEquivalence`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indVertexElements_isKappaFiltered`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indVertexDensityCocone_isColimit`

:::

:::corollary "kerodon_9_3_4_16"
Kerodon Corollary 9.3.4.16（[Tag 06N6](https://kerodon.net/tag/06N6)）。対応表の状態：なし。

型がfilteredとするのはsmallRightUnstraightening。原文が指定するC×\_Chat Chat\_/Xそのものへの比較とfiltered性の同値不変性を引用に揃えていない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indVertexElements_isKappaFiltered`

:::

:::corollary "kerodon_9_3_4_17"
Kerodon Corollary 9.3.4.17（[Tag 0664](https://kerodon.net/tag/0664)）。対応表の状態：なし。

宇宙パラメータのInd・空間・unstraighteningの型は、原文の指定数値κ・λ・μの値圏と同じ余極限・小性条件へ比較されていない。Ind\_κ の各対象は C の小さい κ-filtered 図式の余極限。λ=∞（Ind\_κ）の場合だけ。Mathlib は 1 圏版。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indVertex_has_filteredYonedaPresentation`、`CategoryTheory.Ind.presentation`

:::

:::definition "kerodon_9_3_4_18"
Kerodon Variant 9.3.4.18（[Tag 06N7](https://kerodon.net/tag/06N7)）。対応表の状態：なし。

宇宙パラメータのInd・空間・unstraighteningの型は、原文の指定数値κ・λ・μの値圏と同じ余極限・小性条件へ比較されていない。標準前層圏で各前層は小さい元の圏上の表現可能図式の余極限となる。任意の λ-余完備化 h の像から明示の λ-small な図式で表す型は見つからない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.Cocompletion.presheafDensityCocone_isColimit`

:::

:::lemma_ "kerodon_9_3_4_19" (uses := "kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_4_9_8_10, kerodon_5_1_1_1, kerodon_5_1_4_1, kerodon_5_3_7_3, kerodon_6_3_4_1, kerodon_7_4_5_8, kerodon_7_4_5_13, kerodon_8_4_2_7")
Kerodon Lemma 9.3.4.19（[Tag 065Y](https://kerodon.net/tag/065Y)）。対応表の状態：なし。

宇宙パラメータのInd・空間・unstraighteningの型は、原文の指定数値κ・λ・μの値圏と同じ余極限・小性条件へ比較されていない。各前層 F から小さい全空間と C への right fibration を構成する。任意の正則 λ の濃度制限と、全空間を取る関手が λ-余極限を保つ型は残る。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.smallRightUnstraightening`、`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.smallRightUnstraighteningProjection_rightFibration`

:::

:::lemma_ "kerodon_9_3_4_20" (uses := "kerodon_1_4_0_1, kerodon_9_1_5_16, kerodon_9_3_4_19")
Kerodon Lemma 9.3.4.20（[Tag 065Z](https://kerodon.net/tag/065Z)）。対応表の状態：なし。

HasKappaFilteredElementsはright unstraighteningのfiltered条件。原文の共変積分のcofiltered条件への反転比較と指定数値λ値圏への大きさの比較を含まず、IsIndVertexのiffだけを同じflat性の主張としない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.hasKappaFilteredElements_kappaColimitClosed`

:::

:::lemma_ "kerodon_9_3_4_21" (uses := "kerodon_1_4_0_1, kerodon_4_9_8_12, kerodon_8_4_2_4, kerodon_9_3_4_15, kerodon_9_3_4_20")
Kerodon Lemma 9.3.4.21（[Tag 0660](https://kerodon.net/tag/0660)）。対応表の状態：なし。

HasKappaFilteredElementsはright unstraighteningのfiltered条件。原文の共変積分のcofiltered条件への反転比較と指定数値λ値圏への大きさの比較を含まず、IsIndVertexのiffだけを同じflat性の主張としない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.isIndVertex_iff_hasKappaFilteredElements`

:::

:::corollary "kerodon_9_3_4_23"
Kerodon Corollary 9.3.4.23（[Tag 0662](https://kerodon.net/tag/0662)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の有限余極限を持つ生成圏では、集合値の Ind 前層であることと有限極限保存が同値。原文の一般の κ-flat 空間値関手で既存の κ-small 極限を保つ型は見つからない。

:::

:::proposition "kerodon_9_3_4_25"
Kerodon Proposition 9.3.4.25（[Tag 0665](https://kerodon.net/tag/0665)）。対応表の状態：なし。

HasKappaFilteredElementsはright unstraighteningのfiltered条件。原文の共変積分のcofiltered条件への反転比較と指定数値λ値圏への大きさの比較を含まず、IsIndVertexのiffだけを同じflat性の主張としない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.isIndVertex_iff_hasKappaFilteredElements`

:::

:::corollary "kerodon_9_3_4_26"
Kerodon Corollary 9.3.4.26（[Tag 0666](https://kerodon.net/tag/0666)）。対応表の状態：なし。

HasKappaFilteredElementsはright unstraighteningのfiltered条件。原文の共変積分のcofiltered条件への反転比較と指定数値λ値圏への大きさの比較を含まず、IsIndVertexのiffだけを同じflat性の主張としない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.isIndVertex_iff_hasKappaFilteredElements`

:::

:::corollary "kerodon_9_3_4_27"
Kerodon Corollary 9.3.4.27（[Tag 0667](https://kerodon.net/tag/0667)）。対応表の状態：なし。

HasKappaFilteredElementsはright unstraighteningのfiltered条件。原文の共変積分のcofiltered条件への反転比較を含まず、IsIndVertexのiffだけを同じflat性の主張としない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.isIndVertex_iff_hasKappaFilteredElements`、`CategoryTheory.Limits.isIndObject_iff`

:::

:::corollary "kerodon_9_3_4_28"
Kerodon Corollary 9.3.4.28（[Tag 0668](https://kerodon.net/tag/0668)）。対応表の状態：なし。

HasKappaFilteredElementsはright unstraighteningのfiltered条件。原文の共変積分のcofiltered条件への反転比較を含まず、IsIndVertexのiffだけを同じflat性の主張としない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.isIndVertex_iff_hasKappaFilteredElements`、`CategoryTheory.Limits.isIndObject_iff`

:::

# 9.3.5 Exact Functors

%%%
number := false
tag := "kerodon-9-3-5"
%%%

Kerodon [Tag 0669](https://kerodon.net/tag/0669)

:::definition "kerodon_9_3_5_1" (lean := "CategoryTheory.Limits.PreservesFiniteLimits, CategoryTheory.LeftExactFunctor")
Kerodon Definition 9.3.5.1（[Tag 066A](https://kerodon.net/tag/066A)）。対応表の状態：Mathlib にある。

仮定：通常圏 C,D と関手 F。述語の形成には両圏の有限極限の存在を要求しない（Lean が弱い）。結論：PreservesFiniteLimits F は有限形状の極限保存で、LeftExactFunctor はこれを持つ関手（原文の左完全性と一致）。

:::

:::definition "kerodon_9_3_5_4"
Kerodon Variant 9.3.5.4（[Tag 066D](https://kerodon.net/tag/066D)）。対応表の状態：一部。

PreservesFiniteColimitsは原文前半の通常圏のright exactという定義を直接与える。加法的な場合のexact sequenceによる同値とmonoへの限定は含まない。

宣言：`CategoryTheory.Limits.PreservesFiniteColimits`

:::

:::definition "kerodon_9_3_5_5"
Kerodon Definition 9.3.5.5（[Tag 066E](https://kerodon.net/tag/066E)）。対応表の状態：なし。

引用は通常圏のRepresentablyFlatについての型。原文の準圏のleft/right fibrationによるexact性やSpace値関手との同じ比較を含まず、通常圏での類似結果だけをpartialとしない。

宣言：`CategoryTheory.RepresentablyFlat`

:::

:::definition "kerodon_9_3_5_6"
Kerodon Variant 9.3.5.6（[Tag 066F](https://kerodon.net/tag/066F)）。対応表の状態：なし。

引用は通常圏のRepresentablyCoflatについての型。原文の準圏のleft/right fibrationによるexact性やSpace値関手との同じ比較を含まず、通常圏での類似結果だけをpartialとしない。

宣言：`CategoryTheory.RepresentablyCoflat`

:::

:::definition "kerodon_9_3_5_7"
Kerodon Notation 9.3.5.7（[Tag 066G](https://kerodon.net/tag/066G)）。対応表の状態：なし。

引用は通常圏のLeftExactFunctorについての型。原文の準圏のleft/right fibrationによるexact性やSpace値関手との同じ比較を含まず、通常圏での類似結果だけをpartialとしない。

宣言：`CategoryTheory.LeftExactFunctor`

:::

:::theorem "kerodon_9_3_5_8"
Kerodon Theorem 9.3.5.8（[Tag 066H](https://kerodon.net/tag/066H)）。対応表の状態：なし。

引用は通常圏のpreservesFiniteColimits\_iff\_coflatについての型。原文の準圏のleft/right fibrationによるexact性やSpace値関手との同じ比較を含まず、通常圏での類似結果だけをpartialとしない。

宣言：`CategoryTheory.preservesFiniteColimits_iff_coflat`、`CategoryTheory.preservesFiniteLimits_iff_flat`

:::

:::corollary "kerodon_9_3_5_9"
Kerodon Corollary 9.3.5.9（[Tag 066J](https://kerodon.net/tag/066J)）。対応表の状態：なし。

引用は通常圏のpreservesFiniteLimits\_iff\_flatについての型。原文の準圏のleft/right fibrationによるexact性やSpace値関手との同じ比較を含まず、通常圏での類似結果だけをpartialとしない。

宣言：`CategoryTheory.preservesFiniteLimits_iff_flat`

:::

:::definition "kerodon_9_3_5_10"
Kerodon Definition 9.3.5.10（[Tag 066K](https://kerodon.net/tag/066K)）。対応表の状態：なし。

引用は通常圏のRepresentablyFlatについての型。原文の準圏のleft/right fibrationによるexact性やSpace値関手との同じ比較を含まず、通常圏での類似結果だけをpartialとしない。

宣言：`CategoryTheory.RepresentablyFlat`

:::

:::theorem "kerodon_9_3_5_15"
Kerodon Theorem 9.3.5.15（[Tag 066Q](https://kerodon.net/tag/066Q)）。対応表の状態：なし。

引用は通常圏のRepresentablyFlatについての型。原文の準圏のleft/right fibrationによるexact性やSpace値関手との同じ比較を含まず、通常圏での類似結果だけをpartialとしない。

宣言：`CategoryTheory.RepresentablyFlat`、`CategoryTheory.instIsCofilteredElementsCompOfRepresentablyFlat`

:::

:::corollary "kerodon_9_3_5_17"
Kerodon Corollary 9.3.5.17（[Tag 066S](https://kerodon.net/tag/066S)）。対応表の状態：なし。

引用は通常圏のfinal\_of\_representablyFlatについての型。原文の準圏のleft/right fibrationによるexact性やSpace値関手との同じ比較を含まず、通常圏での類似結果だけをpartialとしない。

宣言：`CategoryTheory.final_of_representablyFlat`

:::

:::corollary "kerodon_9_3_5_18"
Kerodon Corollary 9.3.5.18（[Tag 066T](https://kerodon.net/tag/066T)）。対応表の状態：なし。

引用は通常圏のof\_isRightAdjointについての型。原文の準圏のleft/right fibrationによるexact性やSpace値関手との同じ比較を含まず、通常圏での類似結果だけをpartialとしない。

宣言：`CategoryTheory.RepresentablyFlat.of_isRightAdjoint`

:::

:::corollary "kerodon_9_3_5_19"
Kerodon Corollary 9.3.5.19（[Tag 066U](https://kerodon.net/tag/066U)）。対応表の状態：なし。

右随伴の小極限保存は原文のκ-left exactのleft fibration引戻し条件と異なる結論。両条件の比較を型に持たない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.adjunction_preservesSmallLimits`

:::

:::corollary "kerodon_9_3_5_21"
Kerodon Corollary 9.3.5.21（[Tag 066W](https://kerodon.net/tag/066W)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：一点上の slice の後合成については全小余極限または小 κ-filtered 余極限を保つ型がある。κ-small な任意図式 G の上の slice で、κ-左完全性を移す型は見つからない。

:::

:::corollary "kerodon_9_3_5_22"
Kerodon Corollary 9.3.5.22（[Tag 06N8](https://kerodon.net/tag/06N8)）。対応表の状態：なし。

引用は通常圏のinstRepresentablyCoflatIndYonedaについての型。原文の準圏のleft/right fibrationによるexact性やSpace値関手との同じ比較を含まず、通常圏での類似結果だけをpartialとしない。

宣言：`CategoryTheory.instRepresentablyCoflatIndYoneda`

:::

:::theorem "kerodon_9_3_5_23"
Kerodon Theorem 9.3.5.23（[Tag 066X](https://kerodon.net/tag/066X)）。対応表の状態：なし。

引用は通常圏のpreservesFiniteLimits\_of\_flatについての型。原文の準圏のleft/right fibrationによるexact性やSpace値関手との同じ比較を含まず、通常圏での類似結果だけをpartialとしない。

宣言：`CategoryTheory.preservesFiniteLimits_of_flat`、`CategoryTheory.flat_of_preservesFiniteLimits`

:::

:::corollary "kerodon_9_3_5_25"
Kerodon Corollary 9.3.5.25（[Tag 066Y](https://kerodon.net/tag/066Y)）。対応表の状態：なし。

引用は通常圏のisIndObject\_iff\_preservesFiniteLimitsについての型。原文の準圏のleft/right fibrationによるexact性やSpace値関手との同じ比較を含まず、通常圏での類似結果だけをpartialとしない。

宣言：`CategoryTheory.Limits.isIndObject_iff_preservesFiniteLimits`

:::

:::corollary "kerodon_9_3_5_27"
Kerodon Corollary 9.3.5.27（[Tag 06N9](https://kerodon.net/tag/06N9)）。対応表の状態：なし。

nativeの有限余極限保存にはhexという追加の交換入力があり、数値λのIndκλの対象との比較もない。通常圏Indの有限余極限保存は同じ∞圏の主張ではない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda_finiteColimit_isColimit`、`CategoryTheory.instPreservesFiniteColimitsIndYoneda`

:::

:::corollary "kerodon_9_3_5_28"
Kerodon Corollary 9.3.5.28（[Tag 0670](https://kerodon.net/tag/0670)）。対応表の状態：なし。

引用は通常圏のleftExactFunctorEquivalenceについての型。原文の準圏のleft/right fibrationによるexact性やSpace値関手との同じ比較を含まず、通常圏での類似結果だけをpartialとしない。

宣言：`CategoryTheory.Ind.leftExactFunctorEquivalence`

:::

:::corollary "kerodon_9_3_5_29"
Kerodon Corollary 9.3.5.29（[Tag 0671](https://kerodon.net/tag/0671)）。対応表の状態：なし。

引用は通常圏のleftExactFunctorEquivalenceについての型。原文の準圏のleft/right fibrationによるexact性やSpace値関手との同じ比較を含まず、通常圏での類似結果だけをpartialとしない。

宣言：`CategoryTheory.Ind.leftExactFunctorEquivalence`

:::

:::corollary "kerodon_9_3_5_30"
Kerodon Corollary 9.3.5.30（[Tag 0672](https://kerodon.net/tag/0672)）。対応表の状態：なし。

引用は通常圏のleftExactFunctorEquivalenceについての型。原文の準圏のleft/right fibrationによるexact性やSpace値関手との同じ比較を含まず、通常圏での類似結果だけをpartialとしない。

宣言：`CategoryTheory.Ind.leftExactFunctorEquivalence`

:::

# 9.3.6 Transitivity of Ind-Completion

%%%
number := false
tag := "kerodon-9-3-6"
%%%

Kerodon [Tag 068U](https://kerodon.net/tag/068U)

:::definition "kerodon_9_3_6_2"
Kerodon Construction 9.3.6.2（[Tag 068W](https://kerodon.net/tag/068W)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：一濃度の Ind-Yoneda の回収同型つきの延長と、濃度を上げた accessibility はある。Indκ\^λ の Indλ\^μ から Indκ\^μ への指定包含の延長を関手として作る型は見つからない。

:::

:::proposition "kerodon_9_3_6_3"
Kerodon Proposition 9.3.6.3（[Tag 068X](https://kerodon.net/tag/068X)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：単一の Ind の前層圏への包含は充満忠実。Ind の二段の濃度変更の指定推移関手の充満忠実性は見つからない。

:::

:::theorem "kerodon_9_3_6_4"
Kerodon Theorem 9.3.6.4（[Tag 068Y](https://kerodon.net/tag/068Y)）。対応表の状態：なし。

B6型照合：Ind\_κ(A) が μ-accessible ⇒ ある小さい B で Ind\_μ(B) ≃ Ind\_κ(A) までは得られる。推移性関手の同値の形はない。 原文と同じ対象・射・濃度条件の結論はこの引用型から直接得られない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.indInfinity_isMuAccessible`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.isKappaAccessible_iff_indEquivalence`

:::

:::corollary "kerodon_9_3_6_7"
Kerodon Corollary 9.3.6.7（[Tag 0691](https://kerodon.net/tag/0691)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：小さい冪等完備な生成準圏の場合に単一 κ の compact 対象を Yoneda 像で判定する。λ,μ の比較で小さい Ind の充満部分圏を compact 対象として同定する型は見つからない。

:::

:::corollary "kerodon_9_3_6_8"
Kerodon Corollary 9.3.6.8（[Tag 0692](https://kerodon.net/tag/0692)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：単一 κ の compact 対象の Yoneda 像の判定はある。λ-compact 対象を λ-small な κ-filtered 表示による Ind 部分圏と比較する型は見つからない。

:::

:::corollary "kerodon_9_3_6_10"
Kerodon Corollary 9.3.6.10（[Tag 0694](https://kerodon.net/tag/0694)）。対応表の状態：なし。

引用は通常圏のinstHasColimitsIndOfHasFiniteColimitsについての型。原文の準圏のleft/right fibrationによるexact性やSpace値関手との同じ比較を含まず、通常圏での類似結果だけをpartialとしない。

宣言：`CategoryTheory.instHasColimitsIndOfHasFiniteColimits`

:::

:::corollary "kerodon_9_3_6_11"
Kerodon Corollary 9.3.6.11（[Tag 0695](https://kerodon.net/tag/0695)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：単一 κ の指定 Ind 左 Kan 拡張は小 κ-filtered 余極限を保つ。生成圏の h と H の κ での保存を上限 λ,μ の違いも含めて比較する三条件の iff は見つからない。

:::

:::corollary "kerodon_9_3_6_12"
Kerodon Corollary 9.3.6.12（[Tag 06GB](https://kerodon.net/tag/06GB)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：単一 κ の Ind 左 Kan 拡張による κ-filtered 余極限保存の型はある。両側の二濃度余完備性を仮定して Ind\_\{λ\}\^\{μ\}(F) と F の finitary 性を比較する型は見つからない。

:::

# 9.3.7 Final Objects of Ind-Completions

%%%
number := false
tag := "kerodon-9-3-7"
%%%

Kerodon [Tag 06GD](https://kerodon.net/tag/06GD)

:::theorem "kerodon_9_3_7_1"
Kerodon Theorem 9.3.7.1（[Tag 06GE](https://kerodon.net/tag/06GE)）。対応表の状態：一部。

Cに終対象zがある場合、indYoneda\_isTerminal\_of\_terminalのκ=ℵ0は同じInd(C)の終対象を直接返す。filtered性だけからの場合は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda_isTerminal_of_terminal`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isKappaFiltered_of_isTerminalVertex`

:::

:::proposition "kerodon_9_3_7_2" (uses := "kerodon_1_4_0_1, kerodon_7_4_1_22, kerodon_9_3_2_3")
Kerodon Proposition 9.3.7.2（[Tag 06GF](https://kerodon.net/tag/06GF)）。対応表の状態：なし。

Cの終対象をIndへ送る型はあるが、原文のX=colim Fがその終対象となる同じ余極限の比較を引用に含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda_isTerminal_of_terminal`

:::

:::proposition "kerodon_9_3_7_4"
Kerodon Proposition 9.3.7.4（[Tag 06GH](https://kerodon.net/tag/06GH)）。対応表の状態：なし。

終対象⇒filteredは一般には直接使えるが、引用IndInfinityと原文の数値λのIndκλが同じ対象という比較がない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isKappaFiltered_of_isTerminalVertex`

:::

:::corollary "kerodon_9_3_7_5"
Kerodon Corollary 9.3.7.5（[Tag 06GJ](https://kerodon.net/tag/06GJ)）。対応表の状態：一部。

Cに終対象もあるとindYoneda\_isTerminal\_of\_terminalは同じ標準Indκ(C)の終対象を直接返す。κ-filtered性だけを仮定する向きは含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda_isTerminal_of_terminal`

:::

:::corollary "kerodon_9_3_7_6"
Kerodon Corollary 9.3.7.6（[Tag 06GK](https://kerodon.net/tag/06GK)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Ind の小 κ-filtered 余極限の存在はある。Ind 自体が κ または λ-filtered であることを元の C の κ-filtered 性と比較する三条件の iff は見つからない。

:::

:::theorem "kerodon_9_3_7_9"
Kerodon Theorem 9.3.7.9（[Tag 06GN](https://kerodon.net/tag/06GN)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：元の終対象を Ind-Yoneda が保つ型と、Ind 左 Kan 延長の filtered 余極限保存はある。任意の小 filtered C,D で、Ind(F) の終対象保存を元の F の右余終性で判定する型は見つからない。

:::

:::lemma_ "kerodon_9_3_7_10" (uses := "kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_7_3_8_3, kerodon_7_4_3_11")
Kerodon Lemma 9.3.7.10（[Tag 06GP](https://kerodon.net/tag/06GP)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：任意の関手の右余終性を coslice の弱可縮性で判定する。Ind 上で得た各 coslice の弱可縮性を元の F の coslice へ反映する型は見つからない。

:::

:::proposition "kerodon_9_3_7_11" (uses := "kerodon_1_4_0_1, kerodon_7_2_1_9, kerodon_7_2_2_3, kerodon_9_3_7_2, kerodon_9_3_7_10")
Kerodon Proposition 9.3.7.11（[Tag 06GQ](https://kerodon.net/tag/06GQ)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：一つの Ind の終対象と関手の右余終性は別々に扱う。F と二濃度 Ind 延長の右余終性および終対象保存を比較する三条件の iff は見つからない。

:::

:::corollary "kerodon_9_3_7_12"
Kerodon Corollary 9.3.7.12（[Tag 06GR](https://kerodon.net/tag/06GR)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の終対象への定値関手が Final となる類例と、Ind の Yoneda による終対象保存はある。任意の F の右余終性とその Ind 延長による終対象保存の iff は見つからない。

:::

:::corollary "kerodon_9_3_7_13"
Kerodon Corollary 9.3.7.13（[Tag 06GS](https://kerodon.net/tag/06GS)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：一般の右余終性の coslice 判定はある。sharply below の下で元の F と二濃度 Ind 延長の右余終性を往復する型は見つからない。

:::

