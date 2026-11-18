import Verso
import VersoManual
import VersoBlueprint
import Mathlib.AlgebraicTopology.Quasicategory.InnerFibration
import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
import Mathlib.CategoryTheory.Idempotents.Basic
import Mathlib.CategoryTheory.Idempotents.Karoubi
import Mathlib.CategoryTheory.Limits.Shapes.SplitCoequalizer
import Mathlib.CategoryTheory.Limits.Shapes.SplitEqualizer
import Mathlib.CategoryTheory.Retract
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.InnerAnodyneVertices
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalComposition
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePath
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.InnerAnodyneReplacement
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.Coherent
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.ColimitRetractions
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CompleteSubcomplexRetracts
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CompletenessEquivalence
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.Completion
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CompletionBaseChange
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CompletionCanonicalColimits
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CompletionCofinal
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CompletionLeftCofinal
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CompletionOpposite
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CompletionOppositeGeneral
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CompletionSlice
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CompletionUniqueness
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.FibrationComplete
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.FullSubcomplexSplitting
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.FunctorComplete
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.MissingFaceInnerAnodyne
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.RetractionTriangle
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.SplittingCanonicalColimits
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.SplittingDiagramCone
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.SplittingRestriction
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.StrongSplittingColimit
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.StrongSplittingExistence
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.StrongSplittingLimit
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.StrongSplittingLimitExistence
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.UniversalProperty
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.VertexRetractions
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.Walking
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WeakExtension
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WeakInnerAnodyne
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WeakShape

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "8.5 Retracts and Idempotents" =>
%%%
number := false
tag := "kerodon-8-5"
%%%

Kerodon の 8.5 節（[Tag 03Y9](https://kerodon.net/tag/03Y9)）の項目と、SerrePositivity・Mathlib の宣言との対応。本文は対応表（research/kerodon-coverage）の判定の理由の要約で、Kerodon の本文の写しではない。

*06-catinfty-ind-presentable.html — 5. 冪等完備化*

冪等射は、高次の整合性まで含めて「冪等図式」（Idem の nerve からの図式、\`CoherentIdempotent\`）として扱う（HTT §4.4.5）。

\`\`\`text
def IsIdempotentComplete (X : SSet.\{u\}) : Prop :=
  ∀ d : CoherentIdempotent X, Nonempty (StrongSplitting d)

def IsIdempotentCompletion \{C D : SSet.\{u\}\} (f : C ⟶ D) : Prop :=
  IsIdempotentComplete D ∧ IsFullyFaithful f ∧
    ∀ d : D \_⦋0⦌, ∃ c : C \_⦋0⦌, IsVertexRetractOf d (f.app (Opposite.op ⦋0⦌) c)
\`\`\`

冪等完備化とは、冪等完備な $`D` への充満忠実な $`f` で、$`D` の任意の対象が像の retract になるもの（HTT 5.1.4.2）。

- 内容　／　Lean　／　場所
- 存在：前層 ∞ 圏の中の retract 閉包 $`\mathrm{Idem}(C)`　／　\`idemYoneda\_isIdempotentCompletion\`　／　F2/Idempotent
- 普遍性と一意性　／　\`IsIdempotentCompletion.exists\_extension\`、\`.equivalence\_unique\`　／　F2/Idempotent
- 安定 ∞ 圏の冪等完備化は安定（HA 1.1.3.7）　／　\`idem\_isStable\`、\`IsIdempotentCompletion.isStable\`　／　F2/Idempotent
- $`\mathrm{Ind}(C)^\omega\simeq\mathrm{Idem}(C)`　／　（N-5 e）　／　F2/Compact、F2/Idempotent

これで Cat\<sup\>perf\</sup\>（冪等完備な小さい安定 ∞ 圏）を扱う準備が整っている。

:::definition "kerodon_8_5_0_2" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WalkingSplit, SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingSection_retraction")
Kerodon Construction 8.5.0.2（[Tag 03YB](https://kerodon.net/tag/03YB)）。対応表の状態：本体にある。

*主張*　$`\operatorname{Ret}` は二対象 $`x,y` と射 $`i:y\to x,r:x\to y` からなり、$`ri=\mathrm{id}_y`、$`ir=e` を満たす通常の圏である。非恒等射は $`i,r,e` で、$`e^2=e`、$`ei=i`、$`re=r` となる。

仮定：外部の圏を仮定しない（Kerodon と一致）。結論：WalkingSplit は二対象、像対象の自己射は恒等のみ、元対象の自己射は恒等と冪等、相互の射はそれぞれ一つ。i≫r が像の恒等（Ret の模型として一致）。

:::

# 8.5.1 Retracts in ∞-Categories

%%%
number := false
tag := "kerodon-8-5-1"
%%%

Kerodon [Tag 03YH](https://kerodon.net/tag/03YH)

:::definition "kerodon_8_5_1_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsVertexRetractOf, SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.VertexRetraction")
Kerodon Definition 8.5.1.1（[Tag 03YJ](https://kerodon.net/tag/03YJ)）。対応表の状態：本体にある。

*主張*　無限圏で $`y` が $`x` のレトラクトであるとは、$`i:y\to x`、$`r:x\to y` の合成として $`\mathrm{id}_y` を選べることである。

仮定：単体集合 X と二頂点。原文は X を∞圏とするが、型は hX で定義できる（Lean が弱い）。結論：VertexRetraction y x は hX で i:y→x、r:x→y と i≫r=𝟙 y を持つ。IsVertexRetractOf はその存在（原文と一致）。

:::

:::definition "kerodon_8_5_1_3"
Kerodon Variant 8.5.1.3（[Tag 04K9](https://kerodon.net/tag/04K9)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：指定した二端点の retract から関手圏内で何らかの辺への retract を作る型と、通常圏の射の retract はある。あらかじめ指定した f と g に対する h C の可換四角形から同じ二辺の coherent retract を戻す iff は見つからない。

:::

:::proposition "kerodon_8_5_1_7"
Kerodon Proposition 8.5.1.7（[Tag 03YP](https://kerodon.net/tag/03YP)）。対応表の状態：なし。

通常圏のisomorphismsのretract閉性を原文のh Fun(Δ¹,C)内のretractへ移す、同じ矢を保つArrow(hC)への比較関手を引用に持たない。

宣言：`CategoryTheory.MorphismProperty.IsStableUnderRetracts.isomorphisms`

:::

:::proposition "kerodon_8_5_1_8" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion.canonicalCocones_isColimit")
Kerodon Proposition 8.5.1.8（[Tag 03YQ](https://kerodon.net/tag/03YQ)）。対応表の状態：一部。

*主張*　無限圏 $`C` の全対象が充満部分圏 $`C^0` のある対象のレトラクトなら、任意の関手 $`C\to D` は $`C^0` から左にも右にも Kan 拡張されている。

包含δがさらにIsIdempotentCompletion（標的の冪等完備性も含む）を満たす場合、canonicalCocones\_isColimitは同じFの全標準左Kan余錐の余極限性を直接返す。右Kan側と単なるretract生成だけの一般形は含まない。

:::

:::corollary "kerodon_8_5_1_9"
Kerodon Corollary 8.5.1.9（[Tag 03YR](https://kerodon.net/tag/03YR)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：局所の comma 余錐の相対判定と、固定形状の図式間の retract による絶対余極限の移送はある。入力頂点 X からその retract Y に移るときの二つの comma 形状と相対普遍性を比較する型は見つからない。

:::

:::corollary "kerodon_8_5_1_10"
Kerodon Corollary 8.5.1.10（[Tag 03YS](https://kerodon.net/tag/03YS)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：相対始頂点が retract に閉じ、標準相対左 Kan 性は局所相対余錐の条件である。関手圏で与えた retract が各標準余錐に誘導する比較を含む閉性の型は見つからない。

:::

:::corollary "kerodon_8_5_1_11" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.isColimitCone_of_functorRetraction")
Kerodon Corollary 8.5.1.11（[Tag 03YT](https://kerodon.net/tag/03YT)）。対応表の状態：一部。

*主張*　無限圏の関手 $`U:D\to E` に関する $`U`-余極限図式のレトラクトは、右錐の関手圏の中で取ると、やはり $`U`-余極限図式である。

Uを終対象への射に限ると相対余極限は絶対余極限。isColimitCone\_of\_functorRetractionは同じ全余錐の関手準圏内のretractへ余極限性を直接移す。一般Uは含まない。

:::

:::corollary "kerodon_8_5_1_12" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.isColimitCone_of_functorRetraction")
Kerodon Corollary 8.5.1.12（[Tag 05E6](https://kerodon.net/tag/05E6)）。対応表の状態：本体にある。

*主張*　無限圏への右錐が余極限図式のレトラクトであるなら、その右錐も余極限図式である。

仮定：Quasicategory X、K 上の二つの余錐と、関手圏内での後者への retract データ、後者の IsColimitCone（Kerodon と一致）。結論：isColimitCone\_of\_functorRetraction は retract 側の IsColimitCone（原文と一致）。

:::

:::corollary "kerodon_8_5_1_13"
Kerodon Corollary 8.5.1.13（[Tag 04KA](https://kerodon.net/tag/04KA)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の射の lifting property の retract 閉性と、個別辺の cocartesian ホーン判定はある。Fun(Δ¹,D) の coherent retract からホーン条件を移し、任意の U について同じ辺の cocartesian 性を得る型は見つからない。

:::

:::corollary "kerodon_8_5_1_14" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.PreservesKappaFilteredColimits.of_retract, SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.isColimitCone_of_functorRetraction, CategoryTheory.Retract.map")
Kerodon Corollary 8.5.1.14（[Tag 03YU](https://kerodon.net/tag/03YU)）。対応表の状態：本体にある。

*主張*　無限圏の関手 $`F:C\to D` が $`K` 添字の余極限を保つなら、関手圏での任意のレトラクト $`G` も $`K` 添字の余極限を保つ。

同じFからGへの全関手準圏内のVertexRetractionを、指定K余錐へのprecompositionで写すと全余錐のVertexRetractionになる。isColimitCone\_of\_functorRetractionを適用すれば同じ余錐のG像が余極限。全Kでこの型を使え、κ-filteredだけに限る必要はない。

:::

:::corollary "kerodon_8_5_1_15"
Kerodon Corollary 8.5.1.15（[Tag 05FK](https://kerodon.net/tag/05FK)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：空間の 0-truncated 性の述語と、Kan 複体の可縮性のホモトピー retract への移送はある。任意の準圏で一般の n に関し対象と射の truncation をそれぞれ retract に移す型は見つからない。

:::

:::proposition "kerodon_8_5_1_18"
Kerodon Proposition 8.5.1.18（[Tag 03YV](https://kerodon.net/tag/03YV)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：本質的小性は左ファイブレーションのファイバーに対して定義され、充満忠実像内の対象の retract に別の結果がある。QC の対象の retract による本質的 κ-small 性の閉性は見つからない。

:::

:::corollary "kerodon_8_5_1_20"
Kerodon Corollary 8.5.1.20（[Tag 03YX](https://kerodon.net/tag/03YX)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：左ファイブレーションの各 Kan ファイバーが小さい模型を持つ述語はある。空間圏で本質的 κ-small な Kan 複体の retract に同じ濃度の模型を与える型は見つからない。

:::

:::definition "kerodon_8_5_1_22" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.RetractionTriangle, SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.isVertexRetractOf_iff_retractionTriangle, SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WeakRetractionDiagram")
Kerodon Definition 8.5.1.22（[Tag 03YZ](https://kerodon.net/tag/03YZ)）。対応表の状態：本体にある。

*主張*　無限圏のレトラクション図式は、長辺が恒等射である二単体である。この二単体は中央の対象から両端の対象へのレトラクションを示す。

仮定：X と二頂点。三角形データの定義は quasicategory を要求しない（Lean が弱い）。結論：RetractionTriangle は i と r、および長辺が Edge.id y である CompStruct（原文の 2 単体に一致）。

:::

:::definition "kerodon_8_5_1_27"
Kerodon Notation 8.5.1.27（[Tag 03Z3](https://kerodon.net/tag/03Z3)）。対応表の状態：なし。

WalkingSplitとSplitShapeは原文の特定の三角形σとそのimage Rを構成しない。Retという添字があるだけをこの記法の構成成分と数えない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WalkingSplit`、`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.SplitShape`

:::

:::proposition "kerodon_8_5_1_30" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.weakComparison_innerAnodyne, SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WeakShape")
Kerodon Proposition 8.5.1.30（[Tag 03Z6](https://kerodon.net/tag/03Z6)）。対応表の状態：本体にある。

*主張*　レトラクションの二単体が張る部分単体集合 $`\mathcal R` の $`N(\operatorname{Ret})` への包含は内部無害射である。

仮定：外部の値圏を仮定せず、Ret の長辺を潰した WeakShape からの比較を取る（Kerodon と一致）。結論：weakComparison\_innerAnodyne は R に対応する WeakShape から SplitShape への射の inner anodyne 性（原文と一致）。

:::

:::corollary "kerodon_8_5_1_31" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.weakComparisonRestriction_trivialKanFibration")
Kerodon Corollary 8.5.1.31（[Tag 03Z7](https://kerodon.net/tag/03Z7)）。対応表の状態：本体にある。

*主張*　無限圏 $`C` に対して $`N(\operatorname{Ret})` からの関手を $`\mathcal R` に制限する射は自明な Kan ファイブレーションである。従ってレトラクション図式は $`N(\operatorname{Ret})\to C` に延長でき、その延長は同型を除いて一意である。

仮定：Quasicategory X と WeakShape→SplitShape の標準比較（Kerodon と一致）。結論：その前合成は TrivialKanFibration。WeakShape の押し出し表示は長辺を恒等に固定する原文のファイバー積に対応する（一致）。

:::

:::corollary "kerodon_8_5_1_33"
Kerodon Corollary 8.5.1.33（[Tag 03Z9](https://kerodon.net/tag/03Z9)）。対応表の状態：なし。

weakComparisonRestrictionの余域は長辺を恒等に潰したWeakShapeの関手空間。原文の全Fun(Δ²,C)への同じ制限の充満忠実性と本質的像への比較がない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.weakComparisonRestriction_trivialKanFibration`、`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.weakDiagram_extension_exists`

:::

:::corollary "kerodon_8_5_1_35"
Kerodon Corollary 8.5.1.35（[Tag 03ZA](https://kerodon.net/tag/03ZA)）。対応表の状態：なし。

finiteInternalHomのfiltered余極限保存は有限形状だけ。原文のN(Ret)全体の同じθへの移送の可換式と、filtered余極限での比較の同値性は引用にない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.weakComparisonRestriction_trivialKanFibration`、`SerrePositivity.InfinityCategories.Kerodon.KanComplexes.ComparisonWithTopologicalSpaces.finiteInternalHom_preservesFilteredColimits`

:::

:::lemma_ "kerodon_8_5_1_36" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.missingFaceComplex_innerAnodyne")
Kerodon Lemma 8.5.1.36（[Tag 03ZB](https://kerodon.net/tag/03ZB)）。対応表の状態：本体にある。

*主張*　$`S\subseteq[n]` を取って、$`S` の全頂点を同時には含まない非退化単体で張る $`K\subseteq\Delta^n` を考える。$`i<j<k` で $`i,k\in S,\ j\notin S` となる三頂点があれば $`K\to\Delta^n` は内部無害射である。

仮定：J⊆Fin(n+1)、i\<j\<k、i,k∈J、j∉J（Kerodon と一致）。結論：全 J を含む単体を除いた missingFaceComplex J の包含は inner anodyne（一致）。

:::

# 8.5.2 Idempotents in Ordinary Categories

%%%
number := false
tag := "kerodon-8-5-2"
%%%

Kerodon [Tag 03ZE](https://kerodon.net/tag/03ZE)

:::definition "kerodon_8_5_2_1" (lean := "CategoryTheory.IsIdempotentComplete, CategoryTheory.Idempotents.Karoubi")
Kerodon Definition 8.5.2.1（[Tag 03ZF](https://kerodon.net/tag/03ZF)）。対応表の状態：Mathlib にある。

*主張*　通常の圏の冪等自己射とは、対象 $`x` と $`e:x\to x` で $`e^2=e` を満たすものの組である。

Karoubi Cの対象はX:Cとp:X→Xとp≫p=pというデータそのもの。原文の個別冪等射(X,e)の全型を直接表せるため、圏全体のIsIdempotentCompleteだけという旧引用を置き換える。

:::

:::proposition "kerodon_8_5_2_4" (lean := "CategoryTheory.Idempotents.isIdempotentComplete_iff_hasEqualizer_of_id_and_idempotent, CategoryTheory.IsSplitEqualizer.isEqualizer, CategoryTheory.IsSplitCoequalizer.isCoequalizer")
Kerodon Proposition 8.5.2.4（[Tag 03ZK](https://kerodon.net/tag/03ZK)）。対応表の状態：Mathlib にある。

*主張*　通常の圏で $`i:y\to x,r:x\to y` が $`ri=\mathrm{id}_y` を満たし $`e=ir` とする。$`i` は $`(e,\mathrm{id}_x)` の等化子を、$`r` は同じ対の余等化子を与える。

与えたi,rにi≫r=id、r≫i=eを用いればIsSplitEqualizer e id iとその双対のsplit coequalizerのフィールドを直接満たす。isEqualizerとisCoequalizerは原文の同じiとrの普遍性を直接返す。

:::

:::corollary "kerodon_8_5_2_5" (lean := "CategoryTheory.Idempotents.isIdempotentComplete_iff_hasEqualizer_of_id_and_idempotent, CategoryTheory.IsSplitEqualizer.isEqualizer, CategoryTheory.IsSplitCoequalizer.isCoequalizer")
Kerodon Corollary 8.5.2.5（[Tag 03ZL](https://kerodon.net/tag/03ZL)）。対応表の状態：Mathlib にある。

*主張*　通常の圏の冪等自己射 $`e:x\to x` が分裂すること、$`(e,\mathrm{id}_x)` の等化子が存在すること、その余等化子が存在することは同値である。

分裂からはsplit equalizer/coequalizerの普遍性を用いる。逆に(e,id)のequalizer ιがあればequalizer.lift eでrを作り、lift\_ιとequalizerの単射性でι≫r=id、r≫ι=eを得る。coequalizerは双対。この同じeの三条件のiffを直接得る。

:::

:::corollary "kerodon_8_5_2_6" (lean := "CategoryTheory.Idempotents.isIdempotentComplete_iff_hasEqualizer_of_id_and_idempotent, CategoryTheory.Idempotents.isIdempotentComplete_iff_opposite")
Kerodon Corollary 8.5.2.6（[Tag 03ZM](https://kerodon.net/tag/03ZM)）。対応表の状態：Mathlib にある。

*主張*　等化子を持つ通常の圏、または余等化子を持つ通常の圏では、すべての冪等自己射が分裂する。

仮定：通常圏 C。Lean の判定には全等化子の存在より弱い id と各冪等射の等化子だけで足り、余等化子側は反対圏に移す（Lean が弱い）。結論：IsIdempotentComplete C、すなわち各冪等射の分裂（Kerodon と一致）。

:::

:::definition "kerodon_8_5_2_7" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WalkingIdem, SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingIdempotent_idem")
Kerodon Construction 8.5.2.7（[Tag 03ZN](https://kerodon.net/tag/03ZN)）。対応表の状態：本体にある。

*主張*　普遍冪等射の圏 $`\operatorname{Idem}` は一対象の通常の圏であり、自己射は恒等射と、$`e^2=e` を満たすもう一つの射 $`e` からなる。

仮定：外部の圏は不要（Kerodon と一致）。結論：WalkingIdem の一対象の自己射は恒等と walkingIdempotent で、後者の自己合成は同じ射（原文の Idem と一致）。

:::

# 8.5.3 Idempotents in ∞-Categories

%%%
number := false
tag := "kerodon-8-5-3"
%%%

Kerodon [Tag 03ZS](https://kerodon.net/tag/03ZS)

:::definition "kerodon_8_5_3_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CoherentIdempotent, SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IdemShape")
Kerodon Definition 8.5.3.1（[Tag 03ZT](https://kerodon.net/tag/03ZT)）。対応表の状態：本体にある。

*主張*　無限圏 $`C` の冪等射とは、普遍冪等射の圏の神経からの関手 $`N(\operatorname{Idem})\to C` である。

仮定：C : SSet。原文の∞圏を含み、定義自体は Quasicategory を要求しない（Lean が弱い）。結論：CoherentIdempotent C は nerve WalkingIdem から C への写像の型（原文の冪等図式と一致）。

:::

:::definition "kerodon_8_5_3_5" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.StrongSplitting")
Kerodon Definition 8.5.3.5（[Tag 03ZX](https://kerodon.net/tag/03ZX)）。対応表の状態：本体にある。

*主張*　無限圏の冪等射 $`N(\operatorname{Idem})\to C` の分裂は、その関手を $`N(\operatorname{Ret})` まで延長したものである。延長が存在するとき、その冪等射は分裂するという。

仮定：Idem の nerve 上の d（Kerodon と一致）。結論：StrongSplitting d は Ret の nerve からの写像 s と idemInclusion≫s=d の対（原文の分裂と一致）。

:::

:::proposition "kerodon_8_5_3_8" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.splittingCanonicalCocones_isColimit, SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.splittingDiagramCone_isLimit")
Kerodon Proposition 8.5.3.8（[Tag 0400](https://kerodon.net/tag/0400)）。対応表の状態：一部。

*主張*　無限圏への任意の関手 $`N(\operatorname{Ret})\to C` は、充満部分圏 $`N(\operatorname{Idem})` から左および右 Kan 拡張されている。

splittingCanonicalCocones\_isColimitは原文の同じN(Idem)包含とF̄について全標準左Kan余錐の余極限性、すなわち左Kan側を直接返す。右Kan側はsplittingDiagramConeの別の極限錐だけで代用しない。

:::

:::corollary "kerodon_8_5_3_10" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.strongSplittingRestriction_isFullyFaithful, SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.strongSplittingRestriction_trivialKanFibration_of_complete")
Kerodon Corollary 8.5.3.10（[Tag 0402](https://kerodon.net/tag/0402)）。対応表の状態：本体にある。

*主張*　無限圏 $`C` に対して、$`N(\operatorname{Ret})` からの関手を $`N(\operatorname{Idem})` に制限する関手は充満忠実である。本質像は分裂する冪等射が張る充満部分圏である。

仮定：Quasicategory X。充満忠実性に冪等完備性は不要（Kerodon と一致）。結論：strongSplittingRestriction が充満忠実。StrongSplitting の定義により像の頂点は分裂する図式で、圏全体が冪等完備なら制限は自明 Kan ファイブレーション（充満忠実性と分裂する対象による像の指定は原文と一致）。

:::

:::corollary "kerodon_8_5_3_11" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.nonemptyStrongSplitting_iff_hasLimit, SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.nonemptyStrongSplitting_iff_hasColimit")
Kerodon Corollary 8.5.3.11（[Tag 0403](https://kerodon.net/tag/0403)）。対応表の状態：本体にある。

*主張*　無限圏の冪等射を $`N(\operatorname{Idem})` 上の図式と見ると、分裂すること、極限を持つこと、余極限を持つことは同値である。

仮定：Quasicategory X と Idem 上の d（Kerodon と一致）。結論：Nonempty (StrongSplitting d) と HasLimit d、同じく HasColimit d の iff がそれぞれある（三条件に一致）。

:::

:::corollary "kerodon_8_5_3_12" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.StrongSplitting.postcomposeCocone_isColimit, SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.StrongSplitting.postcomposeCone_isLimit")
Kerodon Corollary 8.5.3.12（[Tag 0404](https://kerodon.net/tag/0404)）。対応表の状態：本体にある。

*主張*　無限圏の冪等射 $`N(\operatorname{Idem})\to C` の図式に極限または余極限があるなら、それは任意の無限圏の関手 $`C\to D` で保たれる。

仮定：指定 d の強い分裂と任意の F:X→Y、Y は quasicategory。d の極限または余極限から分裂を得る二つの iff は 8.5.3.11 の引用で確認（Kerodon と一致）。結論：分裂が与える錐・余錐を後合成した IsLimitCone と IsColimitCone（原文の保存と一致）。

:::

# 8.5.4 Idempotent-Completeness

%%%
number := false
tag := "kerodon-8-5-4"
%%%

Kerodon [Tag 0405](https://kerodon.net/tag/0405)

:::definition "kerodon_8_5_4_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete")
Kerodon Definition 8.5.4.1（[Tag 0406](https://kerodon.net/tag/0406)）。対応表の状態：本体にある。

*主張*　無限圏 $`C` は、すべての冪等射 $`N(\operatorname{Idem})\to C` が分裂するとき冪等完備である。

仮定：C : SSet。述語の形成自体に Quasicategory は不要（Lean が弱い）。結論：IsIdempotentComplete C は全 coherent d の StrongSplitting の存在（原文と一致）。

:::

:::definition "kerodon_8_5_4_3"
Kerodon Variant 8.5.4.3（[Tag 06YL](https://kerodon.net/tag/06YL)）。対応表の状態：なし。

通常圏の冪等完備性の判定と、全N(Idem)図式の極限による準圏の判定はあるが、原文の有限極限と局所n-truncationだけから同じ準圏の冪等完備性を返す型はない。

宣言：`CategoryTheory.Idempotents.isIdempotentComplete_iff_hasEqualizer_of_id_and_idempotent`

:::

:::proposition "kerodon_8_5_4_10" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.fullSubcomplex_isIdempotentComplete, SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.retract_iso_in_complete_fullSubcomplex")
Kerodon Proposition 8.5.4.10（[Tag 040B](https://kerodon.net/tag/040B)）。対応表の状態：一部。

*主張*　冪等完備な無限圏の充満部分圏が、その対象の任意のレトラクトと同型な対象を含むなら、その充満部分圏も冪等完備である。

部分圏の頂点述語をretractに厳密に閉じると強めればfullSubcomplex\_isIdempotentCompleteは同じ全部分準圏の冪等完備性を直接返す。同型な代表だけが含まれる一般形は含まない。

:::

:::proposition "kerodon_8_5_4_11" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.isIdempotentComplete_iff_hasLimits, SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.isIdempotentComplete_iff_hasColimits")
Kerodon Proposition 8.5.4.11（[Tag 040C](https://kerodon.net/tag/040C)）。対応表の状態：本体にある。

*主張*　無限圏が冪等完備であること、$`N(\operatorname{Idem})` 添字の極限を持つこと、同じ形の余極限を持つことは同値である。

仮定：Quasicategory X（Kerodon と一致）。結論：冪等完備性と全ての CoherentIdempotent d の HasLimit d、同じく HasColimit d の二つの iff（原文の三条件と一致）。

:::

:::corollary "kerodon_8_5_4_13" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.isIdempotentComplete_iff_of_equivalence")
Kerodon Corollary 8.5.4.13（[Tag 040E](https://kerodon.net/tag/040E)）。対応表の状態：本体にある。

*主張*　同値な二つの無限圏の一方が冪等完備であることは、他方が冪等完備であることと同値である。

仮定：二つの quasicategory と QCatEquivalence（Kerodon と一致）。結論：IsIdempotentComplete X↔IsIdempotentComplete Y（一致）。

:::

:::corollary "kerodon_8_5_4_14" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.functor_isIdempotentComplete")
Kerodon Corollary 8.5.4.14（[Tag 040F](https://kerodon.net/tag/040F)）。対応表の状態：本体にある。

*主張*　無限圏 $`C` が冪等完備なら、任意の単体集合 $`K` に対して $`\operatorname{Fun}(K,C)` も冪等完備である。

仮定：Quasicategory X、任意の K : SSet、IsIdempotentComplete X（Kerodon と一致）。結論：内部 Hom K⟹X の IsIdempotentComplete（Fun(K,C) と一致）。

:::

:::definition "kerodon_8_5_4_15"
Kerodon Notation 8.5.4.15（[Tag 040H](https://kerodon.net/tag/040H)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：WalkingSplit の有限交互列と WalkingIdem の指定冪等射はある。両方向に無限な整数の spine 上で各辺を同じ冪等射に送る単体写像 Q は見つからない。

:::

:::proposition "kerodon_8_5_4_19"
Kerodon Proposition 8.5.4.19（[Tag 040M](https://kerodon.net/tag/040M)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Idem の nerve から WalkingSplit の nerve への包含が両向きに余終となる型はある。始域が整数 spine で終域が Idem の Q に対する両余終性は見つからない。

:::

:::corollary "kerodon_8_5_4_20"
Kerodon Corollary 8.5.4.20（[Tag 040N](https://kerodon.net/tag/040N)）。対応表の状態：なし。

N(Idem)のκ-filtered性は自然数列の極限・余極限の存在からN(Idem)図式の存在を直接与えない。sequentialな形状との比較が引用にない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.isIdempotentComplete_iff_hasColimits`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.idemShape_isKappaFiltered`

:::

:::proposition "kerodon_8_5_4_25"
Kerodon Proposition 8.5.4.25（[Tag 0605](https://kerodon.net/tag/0605)）。対応表の状態：なし。

functor\_isIdempotentCompleteは全関手準圏の型。原文の指定oriented fiber productとの比較同型を引用で確認していない。恒等への特殊化だけで同じ対象と数えない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.functor_isIdempotentComplete`、`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.sliceOver_isIdempotentComplete`、`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.sliceUnder_isIdempotentComplete`

:::

:::corollary "kerodon_8_5_4_26" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.isIdempotentComplete_of_leftFibration, SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.isIdempotentComplete_of_rightFibration")
Kerodon Corollary 8.5.4.26（[Tag 0606](https://kerodon.net/tag/0606)）。対応表の状態：本体にある。

*主張*　無限圏の左ファイブレーション $`E\to C` の底 $`C` が冪等完備なら、$`E` は冪等完備である。

仮定：左ファイブレーション p と底の IsIdempotentComplete。型では全空間と底の Quasicategory を別途要求しない（Lean が弱い）。結論：全空間の IsIdempotentComplete（原文と一致）。

:::

:::corollary "kerodon_8_5_4_27"
Kerodon Corollary 8.5.4.27（[Tag 0607](https://kerodon.net/tag/0607)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：冪等完備な底から左または右ファイブレーションで全空間へ移す型と同値不変性はある。底を冪等完備とせず二脚の始域だけを仮定する任意のホモトピー引き戻しの型は見つからない。

:::

:::corollary "kerodon_8_5_4_28" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.isIdempotentComplete_of_rightFibration, SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.isIdempotentComplete_of_leftFibration")
Kerodon Corollary 8.5.4.28（[Tag 0608](https://kerodon.net/tag/0608)）。対応表の状態：一部。

*主張*　無限圏の圏論的引き戻し $`C_0\times_C C_1` で、二つの脚の始域 $`C_0,C_1` が冪等完備なら、引き戻しも冪等完備である。

同じG₁:C₀₁→C₁がrightまたはleft fibrationでもあると強めると、isIdempotentComplete\_of\_right/leftFibrationは同じC₀₁の冪等完備性を直接返す。任意のcategorical pullbackだけの場合は含まない。

:::

:::corollary "kerodon_8_5_4_29"
Kerodon Corollary 8.5.4.29（[Tag 060A](https://kerodon.net/tag/060A)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：冪等完備な X を値域とする関手準圏の完備性がある。QC の充満部分圏で非定値の任意の小図式に対して極限閉性を述べる型は見つからない。

:::

# 8.5.5 Idempotent-Completion

%%%
number := false
tag := "kerodon-8-5-5"
%%%

Kerodon [Tag 040T](https://kerodon.net/tag/040T)

:::definition "kerodon_8_5_5_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion")
Kerodon Definition 8.5.5.1（[Tag 040U](https://kerodon.net/tag/040U)）。対応表の状態：本体にある。

*主張*　無限圏の関手 $`H:C\to\widehat C` が冪等完備化を与えるとは、$`H` が充満忠実、$`\widehat C` が冪等完備で、$`\widehat C` のすべての対象がある $`H(x)` のレトラクトであることをいう。

仮定：C,D と写像 f（原文の∞圏間の関手を含む。型の形成は Lean が弱い）。結論：標的の冪等完備性、f の充満忠実性、標的の全頂点が像の retract であることの連言（原文の三条件と一致）。

:::

:::proposition "kerodon_8_5_5_3" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion.pre_isQCatEquivalence, SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion.equivalence_unique")
Kerodon Proposition 8.5.5.3（[Tag 0411](https://kerodon.net/tag/0411)）。対応表の状態：一部。

*主張*　冪等完備な無限圏 $`\widehat C` への関手 $`H:C\to\widehat C` が冪等完備化を与えることは、任意の冪等完備な無限圏 $`D` で前合成 $`\operatorname{Fun}(\widehat C,D)\to\operatorname{Fun}(C,D)` が同値であることと同値である。

IsIdempotentCompletion.pre\_isQCatEquivalenceは原文の同じHについて(a)⇒(b)を直接返す。普遍性から充満忠実性とretract生成を回収する逆向きは含まない。

:::

:::corollary "kerodon_8_5_5_4" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemYoneda_isIdempotentCompletion")
Kerodon Corollary 8.5.5.4（[Tag 040Z](https://kerodon.net/tag/040Z)）。対応表の状態：本体にある。

*主張*　任意の無限圏 $`C` に冪等完備化を与える関手 $`C\to\widehat C` が存在する。

仮定：Quasicategory C（Kerodon と一致）。結論：idemYoneda C は具体的な標的への IsIdempotentCompletion で、原文の存在を満たす（構成を与える分だけ Lean が強い）。

:::

:::proposition "kerodon_8_5_5_5" (uses := "kerodon_1_4_0_1, kerodon_8_3_3_9")
Kerodon Proposition 8.5.5.5（[Tag 040X](https://kerodon.net/tag/040X)）。対応表の状態：なし。

Idem Cはretract presheafを張る部分圏。原文の全小余極限をHom(F,−)が保存するatomを張る部分圏との同定を引用型に持たないため、別の部分圏への冪等完備化だけは数えない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemYoneda_isIdempotentCompletion`、`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.Idem`

:::

:::proposition "kerodon_8_5_5_6"
Kerodon Proposition 8.5.5.6（[Tag 040Y](https://kerodon.net/tag/040Y)）。対応表の状態：なし。

κ-filtered余極限に関するcompact性は、原文のκ-small余極限すべてをHomが保存するatomic性とは異なる条件。idemToCompactの充満忠実性だけから同じ全部分圏への分解は得られない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemPresheaf_isKappaCompact`、`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemToCompactPresheaves_isFullyFaithful`

:::

:::proposition "kerodon_8_5_5_7"
Kerodon Proposition 8.5.5.7（[Tag 0410](https://kerodon.net/tag/0410)）。対応表の状態：なし。

IsLocallySmall.of\_fullyFaithfulの宇宙による局所小性は、原文の指定κにおける本質的κ-small性とのiffへの大きさの比較を含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsLocallySmall.of_fullyFaithful`

:::

:::corollary "kerodon_8_5_5_8"
Kerodon Corollary 8.5.5.8（[Tag 0414](https://kerodon.net/tag/0414)）。対応表の状態：なし。

idemYonedaの対象ごとの存在と前合成普遍性はあるが、原文の指定したQC全体の包含に対する左随伴関手を与える型ではない。対象ごとの普遍性からその全関手を組む比較は引用にない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion.pre_isQCatEquivalence`、`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemYoneda_isIdempotentCompletion`

:::

:::corollary "kerodon_8_5_5_9"
Kerodon Corollary 8.5.5.9（[Tag 0415](https://kerodon.net/tag/0415)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：同じ冪等完備な値域を持つ関手準圏は完備になる。各頂点が異なる準圏を取り得る小図式の QC 内の極限へ完備性を移す型は見つからない。

:::

:::corollary "kerodon_8_5_5_10"
Kerodon Corollary 8.5.5.10（[Tag 0416](https://kerodon.net/tag/0416)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：完備な準圏の適切な充満像の retract closure の完備性と、準圏同値による保存はある。h QCat の対象としての任意の retract に完備性を移す型は見つからない。

:::

# 8.5.6 Morita Equivalence

%%%
number := false
tag := "kerodon-8-5-6"
%%%

Kerodon [Tag 05M8](https://kerodon.net/tag/05M8)

:::definition "kerodon_8_5_6_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion.pre_isQCatEquivalence, SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion")
Kerodon Definition 8.5.6.1（[Tag 05M9](https://kerodon.net/tag/05M9)）。対応表の状態：一部。

*主張*　単体集合の射 $`F:C\to D` は、すべての冪等完備な無限圏 $`E` に対し、前合成 $`\operatorname{Fun}(D,E)\to\operatorname{Fun}(C,E)` が同値であるとき森田同値である。

Fを準圏間の冪等完備化に限ると、pre\_isQCatEquivalenceは任意の冪等完備Eについて同じ前合成同値を直接返し、原文のMorita条件を満たす。任意の単体写像を判定する定義全体は含まない。

:::

:::definition "kerodon_8_5_6_10" (uses := "kerodon_1_1_0_6")
Kerodon Variant 8.5.6.10（[Tag 060F](https://kerodon.net/tag/060F)）。対応表の状態：なし。

小左ファイブレーションの分類と冪等完備化の制限同値は候補だが、原文の任意Morita射と全左ファイブレーションの引戻し写像を同じ分類上の前合成と結ぶ型は引用にない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion.pre_isQCatEquivalence`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityEquivalence`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityDiagram_baseChangeIso`

:::

:::proposition "kerodon_8_5_6_11" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion, SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion.pre_isQCatEquivalence")
Kerodon Proposition 8.5.6.11（[Tag 05MG](https://kerodon.net/tag/05MG)）。対応表の状態：一部。

*主張*　無限圏の関手 $`F:C\to D` が森田同値であることは、充満忠実で、$`D` の全対象が $`F` のある像のレトラクトであることと同値である。

標的Dの冪等完備性を加えると、原文(a)(b)はIsIdempotentCompletion Fを与え、pre\_isQCatEquivalenceが任意の冪等完備Eに対して同じ前合成同値を返す。これはMorita定義の同じテストを満たす向き。逆向きと任意Dは含まない。

:::

:::corollary "kerodon_8_5_6_12"
Kerodon Corollary 8.5.6.12（[Tag 05MH](https://kerodon.net/tag/05MH)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：任意の標的への前合成同値の述語と冪等完備化に対する制限同値はある。任意の単体写像について、Morita 条件に hF の本質的全射性を足すと通常の categorical equivalence になる iff は見つからない。

:::

:::proposition "kerodon_8_5_6_13" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion.op, SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion.op_general, SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion.pre_isQCatEquivalence, SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion")
Kerodon Proposition 8.5.6.13（[Tag 05MJ](https://kerodon.net/tag/05MJ)）。対応表の状態：一部。

*主張*　単体集合の射 $`F` が森田同値であることは、$`F^{\mathrm{op}}` が森田同値であることと同値である。これは、任意の非可算基数 $`\kappa` について $`F^{\mathrm{op}}` に沿う $`\kappa`-小空間値前層の制限が同値であることとも、両端が本質的に $`\kappa`-小さいような一つの非可算正則基数 $`\kappa` でその条件が成り立つこととも同値である。

C,Dを準圏、Fを冪等完備化にも強めるとop\_generalと前合成普遍性からFopも任意冪等完備標的への前合成同値を与える。(1)⇒(2)のこの場合に一致し、κ値前層の条件(3)(4)は含まない。

:::

:::proposition "kerodon_8_5_6_14"
Kerodon Proposition 8.5.6.14（[Tag 05MK](https://kerodon.net/tag/05MK)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：cartesian 辺保存の判定と、冪等完備化に沿う右ファイブレーションの引き戻しを確認した。底写像と各ファイバー写像が Morita のとき、任意の cartesian ファイブレーションの全空間写像に Morita を移す型は見つからない。

:::

:::corollary "kerodon_8_5_6_15" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion.pullback_rightFibration, SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion.pre_isQCatEquivalence, SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion") (uses := "kerodon_1_1_0_6")
Kerodon Corollary 8.5.6.15（[Tag 060G](https://kerodon.net/tag/060G)）。対応表の状態：一部。

*主張*　単体集合の右ファイブレーションに沿って底の森田同値を引き戻した射は森田同値である。

底のFを準圏間のinner fibrationかつ冪等完備化に強めると、pullback\_rightFibrationは同じpullback射を冪等完備化とし、その前合成普遍性が同じ射のMorita条件を返す。任意のMorita射は含まない。

:::

:::corollary "kerodon_8_5_6_16" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion.isRightCofinal, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal.comp") (uses := "kerodon_1_1_0_6, kerodon_7_2_3_13, kerodon_8_5_6_10, kerodon_8_5_6_15")
Kerodon Corollary 8.5.6.16（[Tag 060H](https://kerodon.net/tag/060H)）。対応表の状態：一部。

*主張*　単体集合の森田同値 $`F:C\to C'` と $`G:K\to C` に対し、$`G` が右共終であることと $`FG` が右共終であることは同値である。

Fを準圏間のinner fibrationかつ冪等完備化に強めるとisRightCofinalとcofinalな射の合成から、同じGが右余終ならGFが右余終という向きを直接得る。任意Morita射の場合と反映の向きは含まない。

:::

:::corollary "kerodon_8_5_6_17" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion.isRightCofinal, SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion.isLeftCofinal") (uses := "kerodon_1_1_0_6, kerodon_8_5_6_16")
Kerodon Corollary 8.5.6.17（[Tag 060J](https://kerodon.net/tag/060J)）。対応表の状態：一部。

*主張*　単体集合の任意の森田同値は右共終である。

Fを準圏間の冪等完備化かつinner fibrationに強めるとIsIdempotentCompletion.isRightCofinalは原文の同じFがright cofinalという結論を直接返す。任意Morita射は含まない。

:::

:::corollary "kerodon_8_5_6_18" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion.pullback_rightFibration, SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion.sliceOver")
Kerodon Corollary 8.5.6.18（[Tag 060K](https://kerodon.net/tag/060K)）。対応表の状態：一部。

*主張*　無限圏の冪等完備化 $`C\to C'` と右ファイブレーション $`E'\to C'` を取る。その引き戻し $`E\to C` からの射 $`E\to E'` は $`E` の冪等完備化を与える。

底の同じ冪等完備化Fにinner fibrationを追加すると、pullback\_rightFibrationは指定pullbackの同じ射が冪等完備化となる結論を直接返す。

:::

:::corollary "kerodon_8_5_6_20"
Kerodon Corollary 8.5.6.20（[Tag 060M](https://kerodon.net/tag/060M)）。対応表の状態：なし。

既にある終頂点を完備化へ送る型は、原文のN(Idem)からの右余終図式の存在とのiffではない。idemInclusionも指定Cへの図式とは別の射。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion.map_isTerminalVertex`、`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemInclusion_isRightCofinal`

:::

# 8.5.7 Idempotent Endomorphisms

%%%
number := false
tag := "kerodon-8-5-7"
%%%

Kerodon [Tag 0418](https://kerodon.net/tag/0418)

:::definition "kerodon_8_5_7_1" (lean := "SSet.S1, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv")
Kerodon Notation 8.5.7.1（[Tag 0419](https://kerodon.net/tag/0419)）。対応表の状態：一部。

*主張*　無限圏 $`C` の自己射の無限圏 $`\operatorname{End}_C` は、単体円周 $`\Delta^1/\partial\Delta^1` から $`C` への関手圏である。対象は $`x` と自己射 $`x\to x` の組に対応する。

S1の平行対の余等化子と一般の内部Homから原文のFun(S1,C)というEnd準圏自体を構成できる。対象の自己射データとの全単射の型までは引用しない。

:::

:::definition "kerodon_8_5_7_3"
Kerodon Definition 8.5.7.3（[Tag 041B](https://kerodon.net/tag/041B)）。対応表の状態：なし。

CoherentIdempotent.endomorphismの値はhCの射であり、原文の固定された実際の辺eとの等式ではない。N(Idem)図式だけではその辺を固定した部分圏の条件を直接返さない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CoherentIdempotent`、`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CoherentIdempotent.endomorphism`、`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WalkingIdem`

:::

:::proposition "kerodon_8_5_7_4"
Kerodon Proposition 8.5.7.4（[Tag 041C](https://kerodon.net/tag/041C)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：弱 retract 図式からの強い分裂の延長と、coherent idempotent の一辺の評価はある。End\_C\^\{idm\} へ制限する関手自体の左ホモトピー逆写像は見つからない。

:::

:::corollary "kerodon_8_5_7_5"
Kerodon Corollary 8.5.7.5（[Tag 041D](https://kerodon.net/tag/041D)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：coherent idempotent を指定辺で評価でき、弱 retract 図式を固定した強い分裂の空間は可縮である。分裂のデータを固定せずに End\_C\^\{idm\} と両 core の π₀ を比較する全単射は見つからない。

:::

:::definition "kerodon_8_5_7_8"
Kerodon Definition 8.5.7.8（[Tag 041G](https://kerodon.net/tag/041G)）。対応表の状態：なし。

WeakRetractionDiagramは指定単体形状からの写像で、原文の固定された\[e\]の分裂そのものを型に含まない。StrongSplittingもN(Idem)図式を固定する別の入力。専用述語名の有無ではなく同じ\[e\]への比較の不足。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WeakRetractionDiagram`、`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.StrongSplitting`

:::

:::proposition "kerodon_8_5_7_10"
Kerodon Proposition 8.5.7.10（[Tag 041J](https://kerodon.net/tag/041J)）。対応表の状態：なし。

weakDiagram\_strongSplitting\_existsは弱retract図式を固定する。原文の固定された実際の辺eを同じ分裂に延長する型への比較を含まず、形状の延長だけを同じeのiffとしない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.weakDiagram_strongSplitting_exists`、`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.weakDiagram_extension_exists`

:::

:::definition "kerodon_8_5_7_11"
Kerodon Notation 8.5.7.11（[Tag 041L](https://kerodon.net/tag/041L)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：単体円と WalkingSplit の有限交互列および通常圏の可算余積の telescope はある。整数 spine から単体円への被覆で前合成し、任意の endomorphism を両方向に繰り返す関手は見つからない。

:::

:::proposition "kerodon_8_5_7_12"
Kerodon Proposition 8.5.7.12（[Tag 041M](https://kerodon.net/tag/041M)）。対応表の状態：なし。

N(Idem)図式の極限・余極限と分裂のiffは、原文の整数spine上の指定T\_eの極限と異なる図式。制限による極限の同値への比較が引用にない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.nonemptyStrongSplitting_iff_hasLimit`、`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.nonemptyStrongSplitting_iff_hasColimit`

:::

:::definition "kerodon_8_5_7_14"
Kerodon Definition 8.5.7.14（[Tag 041P](https://kerodon.net/tag/041P)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：coherent idempotent の強い分裂を Idem の nerve の極限または余極限で判定する型はある。任意の e の整数 spine 上の極限・余極限と指定の合成の可逆性を要求する弱分裂の述語は見つからない。

:::

:::definition "kerodon_8_5_7_15"
Kerodon Notation 8.5.7.15（[Tag 041Q](https://kerodon.net/tag/041Q)）。対応表の状態：なし。

WalkingSplitとSplitShapeはRetの模型だが、整数spine上の指定Qを延長する同じQ±とその一意性を返さない。形状自体だけは延長という結論の成分に数えない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WalkingSplit`、`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.SplitShape`

:::

:::lemma_ "kerodon_8_5_7_16"
Kerodon Lemma 8.5.7.16（[Tag 041R](https://kerodon.net/tag/041R)）。対応表の状態：なし。

分裂図式のN(Idem)上の制限錐・余錐の普遍性はあるが、原文の整数spine上の指定Q±Fとは異なる図式。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.splittingDiagramCone_isLimit`、`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.StrongSplitting.cone_isLimit`、`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.StrongSplitting.cocone_isColimit`

:::

:::proposition "kerodon_8_5_7_17"
Kerodon Proposition 8.5.7.17（[Tag 041S](https://kerodon.net/tag/041S)）。対応表の状態：なし。

StrongSplittingのN(Idem)錐・余錐は、原文の整数spineによるweak split条件とその比較合成の可逆性を返さない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.StrongSplitting.cone_isLimit`、`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.StrongSplitting.cocone_isColimit`

:::

:::proposition "kerodon_8_5_7_19"
Kerodon Proposition 8.5.7.19（[Tag 041U](https://kerodon.net/tag/041U)）。対応表の状態：なし。

pre weakComparisonの標的は弱retract図式の全空間であり、原文のweakly splitな自己射のEnd\^wとは別の空間。同じ制限射に対する逆は引用にない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.weakComparisonRestriction_trivialKanFibration`

:::

# 8.5.8 Homotopy Idempotent Endomorphisms

%%%
number := false
tag := "kerodon-8-5-8"
%%%

Kerodon [Tag 041V](https://kerodon.net/tag/041V)

:::definition "kerodon_8_5_8_1"
Kerodon Definition 8.5.8.1（[Tag 041W](https://kerodon.net/tag/041W)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：coherent idempotent の指定辺の h 圏での冪等性は得られる。任意の一辺 e に対して、そのホモトピー類の冪等性だけを要求する独立の述語は見つからない。

:::

:::proposition "kerodon_8_5_8_4"
Kerodon Proposition 8.5.8.4（[Tag 041Z](https://kerodon.net/tag/041Z)）。対応表の状態：なし。

弱retract図式の延長は、指定eの整数spine図式と比較していない。(1)(2)の定義上の言い換えを除き、引用型から同じeのhomotopy idempotence・弱分裂・指定極限との含意を直接得られない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.weakDiagram_strongSplitting_exists`

:::

:::corollary "kerodon_8_5_8_5"
Kerodon Corollary 8.5.8.5（[Tag 0420](https://kerodon.net/tag/0420)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：特定の coherent 冪等図式の極限・余極限の存在を冪等完備性で判定する。単一の homotopy idempotent を入力に、二つの逐次（余）極限の指定合成の可逆性から coherent 冪等性を判定する型は見つからない。

:::

:::corollary "kerodon_8_5_8_6"
Kerodon Corollary 8.5.8.6（[Tag 0421](https://kerodon.net/tag/0421)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：coherent splitting から頂点 retract を得る型と空間の小極限はある。連結な基点つき Kan 複体の homotopy idempotent に split 冪等性を与える型は見つからない。

:::

:::corollary "kerodon_8_5_8_7"
Kerodon Corollary 8.5.8.7（[Tag 0422](https://kerodon.net/tag/0422)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：coherent splitting の頂点 retract は構成される。指定基点への lift の存在と unpointed 冪等性を比較する iff は見つからない。

:::

:::definition "kerodon_8_5_8_9"
Kerodon Definition 8.5.8.9（[Tag 0425](https://kerodon.net/tag/0425)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：二進有理数の実数への変換と一般の同相写像はある。有限の折点を二進有理数に限り、傾きがすべて 2 の整数冪となる区分線形同相写像の定義は見つからない。

:::

:::definition "kerodon_8_5_8_12"
Kerodon Definition 8.5.8.12（[Tag 0428](https://kerodon.net/tag/0428)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：同相写像の通常の合成と二進有理数の実数表示はある。\[0,1\] の同相写像のうち二進折点と指定傾きの条件を満たすものを群にする型は見つからない。

:::

:::definition "kerodon_8_5_8_13"
Kerodon Construction 8.5.8.13（[Tag 0429](https://kerodon.net/tag/0429)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：単位区間の宇宙持ち上げとの同相はある。二進有理数を保つ区間の自己同相の群と、左半区間への縮小と右半区間の恒等を貼る自己準同型の宣言は見つからない。

:::

:::proposition "kerodon_8_5_8_14"
Kerodon Proposition 8.5.8.14（[Tag 042A](https://kerodon.net/tag/042A)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：coherent な場合の h 圏の冪等性と通常圏の nerve 写像はある。Thompson 群の指定 α から BAut\_Dy 上のホモトピー冪等な e を作る型は見つからない。

:::

:::proposition "kerodon_8_5_8_15"
Kerodon Proposition 8.5.8.15（[Tag 042B](https://kerodon.net/tag/042B)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：coherent idempotent の辺評価と弱 retract 図式からの強い分裂の延長はある。指定した BAut\_Dy 上の e が coherent idempotent に由来しないことを示す型は見つからない。

:::

# 8.5.9 Partial Idempotents

%%%
number := false
tag := "kerodon-8-5-9"
%%%

Kerodon [Tag 042C](https://kerodon.net/tag/042C)

:::theorem "kerodon_8_5_9_4" (lean := "SSet.innerAnodyneExtensions_eq_llp_rlp, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.innerAnodyne_vertex_bijective, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.exists_innerAnodyne_innerFibration_factorization, SSet.quasicategory_of_innerFibration")
Kerodon Theorem 8.5.9.4（[Tag 042G](https://kerodon.net/tag/042G)）。対応表の状態：一部。

*主張*　$`n\geq3` で、冪等射の神経の $`n` 次骨格の包含は、無限圏 $`E` への内部無害射と $`E\to N(\operatorname{Idem})` に分解できる。前者は次元 $`<n` の単体で全単射であり、後者は右逆を持つ。

exists\_innerAnodyne\_innerFibration\_factorizationを指定骨格包含に適用すると、同じ射のinner anodyneとinner fibrationへの分解を直接得る。N(Idem)が準圏なので中間も準圏。低次数の全単射と右逆Vは含まない。

:::

:::corollary "kerodon_8_5_9_6"
Kerodon Corollary 8.5.9.6（[Tag 042J](https://kerodon.net/tag/042J)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：骨格と、retract を含む弱い図式を強い分裂へ延長する型はある。Idem の (n−1) 骨格の写像について n 骨格への延長だけで全 Idem への延長が得られる iff は見つからない。

:::

:::corollary "kerodon_8_5_9_8"
Kerodon Corollary 8.5.9.8（[Tag 042L](https://kerodon.net/tag/042L)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：coherent idempotent の指定辺と弱い retract 図式の強い延長はある。任意の辺について Idem の 3 骨格への延長と全 coherent idempotent への延長を結ぶ iff は見つからない。

:::

:::corollary "kerodon_8_5_9_9"
Kerodon Corollary 8.5.9.9（[Tag 042M](https://kerodon.net/tag/042M)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：有限形状の内部 Hom は通常の filtered 余極限を保ち、Idem の全形状での余極限による完備性の判定はある。無限の N(Idem) に対する指定比較 θ が準圏同値となる型は見つからない。

:::

:::corollary "kerodon_8_5_9_10"
Kerodon Corollary 8.5.9.10（[Tag 042N](https://kerodon.net/tag/042N)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：単独の準圏で Idem の余極限により冪等完備性を判定し、厳密な filtered 余極限が準圏であることは確認できる。その頂点で冪等完備性を保存する型は見つからない。

:::

:::lemma_ "kerodon_8_5_9_11" (lean := "SSet.innerAnodyneExtensions_eq_llp_rlp, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.innerAnodyne_vertex_bijective, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.exists_innerAnodyne_innerFibration_factorization, SSet.quasicategory_of_innerFibration")
Kerodon Lemma 8.5.9.11（[Tag 042Q](https://kerodon.net/tag/042Q)）。対応表の状態：一部。

*主張*　$`n\geq0` で、単体集合 $`K` の次元 $`\leq n` の内部角がすべて延長できるなら、無限圏への内部無害射 $`K\to E` で、次元 $`<n` の単体では全単射となるものが存在する。

n=1に限ると終対象へのinner anodyne/inner fibration分解から同じKの準圏置換を得て、innerAnodyne\_vertex\_bijectiveが必要な全次数\<1の全単射を返す。一般nでの低次数保存は含まない。

:::

:::proposition "kerodon_8_5_9_13"
Kerodon Proposition 8.5.9.13（[Tag 042S](https://kerodon.net/tag/042S)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：coherent idempotent の辺の h 圏での冪等性と、内 anodyne の頂点での全単射性はある。指定された 3 骨格写像の 2 次以下の全単射性からその辺の coherent idempotent 性を得る型は見つからない。

:::

# 8.5.10 The Thompson Groupoid

%%%
number := false
tag := "kerodon-8-5-10"
%%%

Kerodon [Tag 042T](https://kerodon.net/tag/042T)

:::definition "kerodon_8_5_10_1"
Kerodon Definition 8.5.10.1（[Tag 042U](https://kerodon.net/tag/042U)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：二進有理数の実数表示と一般の同相写像はある。\[0,s\] を対象とし二進折点と傾きを制限した同相写像を射とする Thompson 亜群の定義は見つからない。

:::

:::definition "kerodon_8_5_10_3"
Kerodon Construction 8.5.10.3（[Tag 042W](https://kerodon.net/tag/042W)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：単位を備えるモノイド圏の構造と二進有理数の実数での加法はある。二つの区間同相写像を指定の平行移動で貼り、零区間を厳密単位とする結合関手は見つからない。

:::

:::definition "kerodon_8_5_10_4"
Kerodon Notation 8.5.10.4（[Tag 042X](https://kerodon.net/tag/042X)）。対応表の状態：なし。

MonoidalSingleObjは任意のモノイド圏からの通常の構成で、原文の具体的Dy、指定射x↦2x、豊穣からDuskinへの同じ写像Fを返す型ではない。

宣言：`CategoryTheory.MonoidalSingleObj`

:::

:::theorem "kerodon_8_5_10_5"
Kerodon Theorem 8.5.10.5（[Tag 042Y](https://kerodon.net/tag/042Y)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：前合成同値の一般述語とモノイド圏の delooping はある。Idem の 2 骨格から BDy の Duskin nerve への指定写像の categorical equivalence は見つからない。

:::

:::corollary "kerodon_8_5_10_6"
Kerodon Corollary 8.5.10.6（[Tag 042Z](https://kerodon.net/tag/042Z)）。対応表の状態：なし。

一般の前合成のtrivial Kan判定は、原文の具体的BDyの2骨格包含に対する前合成同値の仮定を供給しない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence.trivialKanFibration_pre`

:::

:::corollary "kerodon_8_5_10_7"
Kerodon Corollary 8.5.10.7（[Tag 0430](https://kerodon.net/tag/0430)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：coherent idempotent の辺の h 圏での冪等性と一対象双圏はある。任意のホモトピー冪等 e を BDy の Duskin nerve からの関手の指定辺の像として特徴づける型は見つからない。

:::

:::definition "kerodon_8_5_10_9"
Kerodon Notation 8.5.10.9（[Tag 0432](https://kerodon.net/tag/0432)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：一般の単体豊穣圏の coherent nerve と通常のモノイド圏の delooping はある。2 骨格の path category から N(Dy) への単体モノイド準同型で e と h の像を指定する型は見つからない。

:::

:::proposition "kerodon_8_5_10_11"
Kerodon Proposition 8.5.10.11（[Tag 0434](https://kerodon.net/tag/0434)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：弱ホモトピー同値の述語と coherent nerve はある。2 骨格の path category の自己射から Thompson 亜群の nerve への指定準同型 φ が弱ホモトピー同値となる型は見つからない。

:::

:::definition "kerodon_8_5_10_12"
Kerodon Notation 8.5.10.12（[Tag 0435](https://kerodon.net/tag/0435)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：二進有理数の実数表示と区間同相に使える一般の型はある。整数長区間の各単位区間で x↦(x+a)/2\^b の形を要求する射と、Dy₊ の部分圏は見つからない。

:::

:::proposition "kerodon_8_5_10_15"
Kerodon Proposition 8.5.10.15（[Tag 0438](https://kerodon.net/tag/0438)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：内 anodyne の一般的な超限合成による判定と coherent nerve はある。指定 φ を N(Dy₊) 経由で因数分解し、その第一因子を内 anodyne とする型は見つからない。

:::

:::definition "kerodon_8_5_10_16"
Kerodon Notation 8.5.10.16（[Tag 0439](https://kerodon.net/tag/0439)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：同相写像の逆と二進有理数の加法はある。有限集合 J が指定する単位区間だけ傾きを 2 とする b\_J およびその逆を elementary contraction とする型は見つからない。

:::

:::lemma_ "kerodon_8_5_10_18"
Kerodon Lemma 8.5.10.18（[Tag 043B](https://kerodon.net/tag/043B)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：内 anodyne の一般の生成条件と coherent nerve はある。N(Dy₊) で elementary contraction を指定し、短い射のクラスの条件を検証する型は見つからない。

:::

