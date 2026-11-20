-- audit2: 7d0968dad3e8672a6213dc0e508983c17f14eaaa inputs sha256 b3e2631992a041109ef8ab3a4836cc24453830556fb4a9c55f9a166f68e2cde1
-- audit2 baselines: 23cbebdfe9d75717f3f248bb0069ebd9dc9bbef6, cddf4d2dac6a409e64204686cf743e703350a6f6
import Verso
import VersoManual
import VersoBlueprint
import Mathlib.CategoryTheory.Presentable.Finite
import Mathlib.CategoryTheory.Presentable.IsCardinalFiltered
import Mathlib.CategoryTheory.Presentable.Type
import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.Definition
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningRepresentation
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.FilteredEquivalence
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.FilteredInfinity
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.FilteredPosetNerve
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.FilteredWeakContractibility
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.KappaFilteredCoslices
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.TerminalFiltered
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.Definition
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.FiniteColimitClosureUnconditional
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.FunctorCompactEndReduction
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IdemFiltered
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IndCompact
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.NativeFilteredPreservation
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.Preservation
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.RepresentableCoslice
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.RepresentableRetractions
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.SmallQuasicategoryColimitCompact
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.Subcategory
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.YonedaCompact
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.ContinuousFunctorRestriction
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.FilteredClosure
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.FilteredElementsClosure
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.FinitePosetDiagramPresentation
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.FiniteYonedaColimitPreservation
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndComparisonEquivalence
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndComparisonFullyFaithful
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndContinuousLeftKan
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndLeftKanExtension
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndLeftKanPreservation
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndRestrictionEquivalence
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.KappaColimits
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.PresheafSubcategory
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.SingleFilteredPresentation
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.Aleph0CardinalChangeBound
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CompactModelGenerators
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IndCardinalChange
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.NativeBaseChangePreservation
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresheafDensityLeftKanCriterion
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresheafPresentable
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallCompactModels
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallLimitFamilyPreservation
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.FilteredDiagonalCofinality
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftCanonicalMapping
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ColimitCoconeRestriction
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.UniversalityOfColimits.FilteredColimitFiniteLimitPreservation
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.Completion
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.StrongSplittingExistence
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.UniversalProperty

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "HTT 5.3 ∞-Categories of Inductive Limits" =>
%%%
number := false
tag := "htt-5-3"
%%%

HTT 5.3 の項目のうち、本体か Mathlib に対応があるもの（対応表 `research/htt-coverage` の状態が「なし」でないもの）。本文は日本語で独立に書いた要約と解説で、原典の本文の写しではない。

*presentable-route.html — 6. Gabriel–Ulmer と Lurie–Simpson*

§5 の準備 (a)「presentable なら前層圏の反射的局所化」は、presentable の同値な特徴づけを与える定理の一部である。証明の核は、§4 ④ の realization ⊣ nerve を $`\kappa`-コンパクト対象に適用し、nerve が充満忠実になる（コンパクト対象が稠密である）ことを示すことにある。

*presentable-route.html — 6. Gabriel–Ulmer と Lurie–Simpson — 主張*

*1 圏（Gabriel–Ulmer、Adámek–Rosický の形）*．局所小な $`\mathcal C` と正則基数 $`\kappa` について次は同値。

- 局所 $`\kappa`-表示可能：余完備で、$`\kappa`-コンパクト対象の小さい集合 $`G` があり、全ての対象が $`G` の対象の $`\kappa`-filtered 余極限。

- $`\mathcal C\simeq\mathrm{Ind}_\kappa(A)`、$`A` は $`\kappa`-小さい余極限を持つ小さい圏（$`A=\mathcal C^\kappa`）。$`\mathrm{Ind}_\kappa(A)` は $`\kappa`-小さい極限を保つ前層の圏と一致する。

- $`\mathcal C` はある $`\mathcal P(A)` の反射的な充満部分圏で、$`\kappa`-filtered 余極限で閉じている。

（本質的に代数的な理論のモデルの圏、という特徴づけもある。）

*∞ 圏（Lurie–Simpson、HTT Thm 5.5.1.1）*．∞ 圏 $`\mathcal C` について次は同値。

- accessible で小さい余極限を持つ（presentable の定義）。

- ある $`\kappa` について $`\mathcal C\simeq\mathrm{Ind}_\kappa(\mathcal C^\kappa)`、$`\mathcal C^\kappa` は本質的に小さく $`\kappa`-小さい余極限を持つ。

- ある小さい $`A` について、$`\mathcal C` は $`\mathcal P(A)` の accessible な反射的局所化。

- ある小さい $`A` と $`\mathcal P(A)` の射の小さい集合 $`S` について $`\mathcal C\simeq S^{-1}\mathcal P(A)`（$`S` 局所対象の充満部分圏）。

- 局所小で小さい余極限を持ち、$`\kappa`-コンパクト対象の小さい集合が余極限で生成する。

*presentable-route.html — 6. Gabriel–Ulmer と Lurie–Simpson — 証明の核：nerve の充満忠実性*

$`A:=\mathcal C^\kappa`、包含 $`j\colon A\hookrightarrow\mathcal C` とし、§4 の普遍性から
$$`L=\mathrm{Lan}_y\,j\colon\ \mathcal P(A)\ \rightleftarrows\ \mathcal C\ \colon N,\qquad N(c)=\mathrm{Hom}_{\mathcal C}(j(-),c).`
$`N` が充満忠実 ⇔ 余単位 $`LN(c)\to c` が同型 ⇔
$$`\operatorname*{colim}_{(a\to c)\in A/c}a\ \xrightarrow{\ \sim\ }\ c\qquad\text{（稠密性）}.`

*1 圏での証明*．

- $`A/c` は $`\kappa`-filtered：$`\kappa`-小さい図式 $`(a_i\to c)` について $`\operatorname{colim}a_i\in A` が余錐を与える。

- 全ての対象はコンパクト対象の余極限なので、同型は $`\mathrm{Hom}(a,-)`（$`a\in A`）で判定できる。

- $`a` がコンパクトで $`A/c` が filtered なので $`\mathrm{Hom}(a,\operatorname{colim}_{A/c}a')\cong\operatorname{colim}_{A/c}\mathrm{Hom}(a,a')`。これから $`\mathrm{Hom}(a,c)` への写像は、$`(a\xrightarrow{g}c,\mathrm{id}_a)` により全射、filtered 性により単射。

*像*：$`N` の像は $`\kappa`-小さい極限を保つ前層。$`\mathrm{Set}` で $`\kappa`-filtered 余極限と $`\kappa`-小さい極限が可換なので、この部分圏は $`\kappa`-filtered 余極限で閉じる。*逆向き*：反射的局所化 $`L\dashv i`（$`i` が $`\kappa`-filtered 余極限を保つ）があれば、$`\mathcal C` の余極限は $`L(\operatorname{colim})` で得られ、$`\mathrm{Hom}(L\,y(a),c)\cong(ic)(a)` から $`L\,y(a)` は $`\kappa`-コンパクトで生成元になる。

# 5.3.1 Filtered ∞-Categories

%%%
number := false
tag := "htt-5-3-1"
%%%

:::definition "htt_5_3_1_7" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsFilteredInfinity, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isKappaFiltered_aleph0_iff")
*HTT 定義 5.3.1.7*　κ フィルター準圏と有限余錐の定義（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=400)）。対応表の状態：本体にある。

*主張*　正則基数 $`\kappa` に対して、∞ 圏が $`\kappa`-filtered であるとは、すべての $`\kappa`-小図式が右錐へ延びることで、filtered は $`\omega`-filtered を指す。

仮定：正則 κ と準圏 C（Lean はクラス形成に正則性を要求せず、この点で弱い）。結論：全 κ-small 単体集合 K の図式に同じ図式を延長する余錐が存在する κ-filtered 性、および κ=ℵ₀ と有限形状の filtered 性の同値（HTT と一致）。通常の圏の神経だけには試験形状を制限しない。

要求するのは余錐の存在であり、その余錐が余極限となることではない。小図式全体から一つの共通の頂点へ整合的に写せる条件である。

:::

:::proposition "htt_5_3_1_8" (lean := "CategoryTheory.isCardinalFiltered_preorder, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isKappaFiltered_nerve_of_cardinalFiltered")
*HTT 例 5.3.1.8*　半順序の小部分集合の上界による判定（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=401)）。対応表の状態：一部（direction）。

*主張*　半順序集合の nerve が $`\kappa`-filtered であることは、その任意の $`\kappa`-小部分集合が上界を持つことと同値である。

KB-W2原文・型再照合：仮定：正則 κ と半順序 A の全 κ-small 部分集合に上界が存在する（HTT の一方の条件と一致）。結論：N(A) が全 κ-small 単体図式について κ-filtered（Lean が弱い：上界条件⇒神経の κ-filtered 性の向き）。Mathlib の任意の小さい族への共通上界から IsCardinalFiltered を得る型と、その神経への宣言を合成する。

半順序集合では比較射があると一意なので、共通の上界さえあれば図式と両立する余錐も決まる。

:::

:::proposition "htt_5_3_1_9" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.restrict, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.idemShape_isKappaFiltered")
*HTT 例 5.3.1.9*　右錐の収縮と冪等図式のフィルター性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=401)）。対応表の状態：本体にある。

*主張*　右錐への包含が左逆を持つ ∞ 圏はすべての正則基数について filtered であり、$`\mathrm{Idem}` がその例である。

仮定：C→C⋆Δ⁰ に左逆がある準圏 C（HTT と一致）。結論：全正則 κ について C は κ-filtered、特に Idem もそうである（HTT と一致）。左逆は恒等図式の JoinCocone そのものであり、任意の f:K→C に restrict した余錐が元の f を延長する。Idem には元の全 coherent 図式について同じ結論の明示宣言がある。

元の図式をまず右錐に入れて余錐を作り、左逆で元の圏に戻す。包含上で恒等なので、元の図式は変更されない。

:::

:::proposition "htt_5_3_1_10" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.idemShape_isKappaFiltered, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.HasSmallKappaFilteredColimits, SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.strongSplitting_exists_of_hasColimit")
*HTT 注意 5.3.1.10*　フィルター付き余極限と冪等完備性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=401)）。対応表の状態：本体にある。

*主張*　小さい $`\kappa`-filtered 余極限を持つ ∞ 圏は冪等完備である。

仮定：正則 κ と小さい κ-filtered 余極限を持つ準圏 C（HTT と一致）。結論：C の全 coherent 冪等図式が強く分裂し、C は冪等完備（HTT と一致）。元の Idem が κ-filtered なので各冪等図式の余極限が仮定の一例となり、その同じ図式の余極限から strongSplitting\_exists\_of\_hasColimit を適用する。宇宙を合わせて元の小さい図式を扱う。

冪等子の添字 $`\mathrm{Idem}` は $`\kappa`-filtered なので、仮定の中にその図式の余極限が含まれる。冪等子の分裂を余極限で判定できる。

:::

:::proposition "htt_5_3_1_11" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isKappaFiltered_iff_of_isQCatEquivalence")
*HTT 注意 5.3.1.11*　余スライスの非空性と同値不変性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=401)）。対応表の状態：本体にある。

*主張*　$`\kappa`-filtered 性はすべての $`\kappa`-小図式について余錐の圏が非空であることと言い換えられ、圏同値で不変である。

仮定：κ-small な図式 p と圏同値 C→C′（HTT と一致）。結論：κ-filtered 性は各 p の余錐すなわち Cp/ の頂点の非空性であり、同じ κ の filtered 性は圏同値で保たれ反映される（HTT と一致）。同型に限らず、ホモトピー逆と全関手同型を持つ同値を扱う。

同値な値域で同じ形の図式を比較すると、余錐の圏も同値になる。とくに余錐を一つ持つという条件を両側で移せる。

:::

:::proposition "htt_5_3_1_17" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isKappaFiltered_of_isTerminalVertex")
*HTT 注意 5.3.1.17*　終対象を持つ準圏の κ フィルター性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=404)）。対応表の状態：本体にある。

*主張*　終対象を持つ ∞ 圏は任意の正則基数について $`\kappa`-filtered である。

仮定：終対象 x を持つ準圏 C と正則 κ（Lean は κ の正則性も要求せず弱い）。結論：同じ C は κ-filtered（HTT と一致）。全ての小さい coherent 図式の余錐を同じ終対象へ延長するので、通常の神経や有限形状には限定しない。

どの小図式からも終対象へ向かう余錐がある。余錐の存在の判定だけを使うので、図式ごとの余極限の有無は問わない。

:::

:::proposition "htt_5_3_1_18" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.exists_cofinal_kappaFiltered_poset")
*HTT 命題 5.3.1.18*　フィルター半順序による共終表示（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=404)）。対応表の状態：本体にある。

*主張*　$`\kappa`-filtered な ∞ 圏には、$`\kappa`-filtered 半順序集合の nerve からの共終写像がある。

仮定：正則 κ と小さい κ-filtered 準圏 C（HTT と一致）。結論：小さい κ-filtered 半順序 I と N(I)→C の共終写像（HTT と一致）。I の通常の IsCardinalFiltered、元の神経の全 κ-small 図式に対する IsKappaFiltered、元の写像の IsRightCofinal が同じ存在命題に含まれる。

元の圏の高次の構造が半順序集合に置き換わるという意味ではなく、余極限を調べる添字を共終な半順序集合で選び直せる。

:::

:::lemma_ "htt_5_3_1_20" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isWeaklyContractible_of_isFilteredInfinity")
*HTT 補題 5.3.1.20*　フィルター準圏の弱可縮性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=406)）。対応表の状態：本体にある。

*主張*　filtered な ∞ 圏は弱可縮である。

仮定：filtered 準圏 C（HTT と一致）。結論：元の単体集合 C の弱可縮性（HTT と一致）。非空性と有限形状の零ホモトピーによる Kan 置換の可縮性から得る型で、C 自身の Kan 性を追加しない。

有限な形の図式が余錐に延びることを用いて、空間として見たときの有限次元の球面の写像を零ホモトピーにする。

:::

:::lemma_ "htt_5_3_1_21" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isKappaFiltered_sliceUnder")
*HTT 補題 5.3.1.21*　小図式の余スライスの κ フィルター性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=406)）。対応表の状態：本体にある。

*主張*　$`\kappa`-filtered な ∞ 圏で、$`\kappa`-小図式 $`p` の余錐の圏 $`\mathcal C_{p/}` も $`\kappa`-filtered である。

仮定：正則 κ、κ-filtered な準圏 C と κ-small な形状 K の図式 p（HTT と一致）。結論：同じ p の余スライス Cp/ が κ-filtered（HTT と一致）。二つの κ-small 形状の join を使い、元の図式を保つ余錐を与える。

複数の余錐を束ねる図式は、元の固定図式を含む一つの小図式として読むことができる。元の圏で共通の頂点を与えれば余錐の圏でも共通の頂点を得る。

:::

:::proposition "htt_5_3_1_22" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isRightCofinal_constantDiagram_of_kappaFiltered")
*HTT 命題 5.3.1.22*　小形状の対角関手によるフィルター性の判定（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=406)）。対応表の状態：一部（direction）。

*主張*　∞ 圏 $`\mathcal C` が $`\kappa`-filtered であることは、すべての $`\kappa`-小 $`K` について定値図式を作る対角 $`\mathcal C\to\operatorname{Fun}(K,\mathcal C)` が共終であることと同値である。

KB-W2原文・型再照合：仮定：正則 κ、κ-filtered 準圏 C、κ-small な単体集合 K（HTT の一方の条件と一致）。結論：同じ対角 C→Fun(K,C) が共終（Lean が弱い：filtered 性⇒全対角の共終性の向き）。原典の逆方向を構造として返す宣言はここでは確認していない。

関手圏で図式から定値図式への写像は余錐である。対角の共終性に現れる各図式のコンマ圏は、まさに余錐を集めた圏になる。

:::

# 5.3.3 Filtered Colimits

%%%
number := false
tag := "htt-5-3-3"
%%%

:::definition "htt_5_3_3_1" (lean := "SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits")
*HTT 定義 5.3.3.1*　κ 小余極限を持つ準圏の定義（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=411)）。対応表の状態：一部（stronger-hyp）。

*主張*　∞ 圏が $`\kappa`-closed であるとは、$`\kappa`-小形の図式の余極限をすべて持つことである。

KB-W2原文・型再照合：仮定：準圏 C が全小余極限を持つ（Lean が強い：κ-small な形状だけでなく全小形状に余極限を要求）。結論：κ-small な全図式が同じ図式を延長する余極限錐を持つ κ-closed 性（この場合に定義の条件と一致）。HasSmallKappaFilteredColimits は添字が κ-filtered の条件であり、κ-small と取り違えていない。

固定した形について余極限余錐を選ぶ自由度は可縮である。したがって余錐を選んで錐点を評価する操作を、余極限関手としてまとめられる。

:::

:::proposition "htt_5_3_3_3" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.UniversalityOfColimits.smallSpaceFilteredColimit_map_isLimit_finite, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.UniversalityOfColimits.smallSpaceColimitFunctor") (uses := "htt_1_1_2_4, htt_5_3_1_7")
*HTT 命題 5.3.3.3*　フィルター余極限と小極限の交換による判定（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=412)）。対応表の状態：一部（special）。

*主張*　∞ 圏 $`I` が $`\kappa`-filtered であることは、空間値 $`I`-図式の余極限関手が $`\kappa`-小極限を保つことと同値である。

KB-W2原文・型再照合：仮定：I が filtered 準圏（Lean が強い：原典の正則 κ を ℵ₀ に固定）。結論：元の空間値余極限関手が全有限単体集合形状の元の指定極限錐を保存する（この場合に (1)⇒(2) が一致）。通常の半順序の神経や積・引き戻しだけに形状を限定しない。任意の正則 κ の全 κ-small 形状、および保存から I の filtered 性を得る逆方向は含まない。

filtered 性を添字圏の図式延長で検査する代わりに、その添字で取る空間の余極限が、別の小形の極限と交換できるかを見る。

:::

# 5.3.4 Compact Objects

%%%
number := false
tag := "htt-5-3-4"
%%%

:::proposition "htt_5_3_4_1" (lean := "CategoryTheory.Types.isCardinalPresentable_iff, CategoryTheory.isFinitelyPresentable_iff_preservesFilteredColimits")
*HTT 例 5.3.4.1*　集合のコンパクト性と有限性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=413)）。対応表の状態：Mathlib にある。

*主張*　集合圏でコンパクトな対象はちょうど有限集合である。

仮定：集合 X、κ=ℵ₀（HTT と一致）。結論：共変 Hom が filtered 余極限を保つことと \|X\|\<ℵ₀、すなわち有限性が同値（一致）。通常の圏について述べた原典の例そのものであり、準圏との比較を追加していない。

有限集合からの写像は有限個の点の像で決まり、filtered 余極限の一段でそれらを同時に表せる。無限集合では有限部分集合の図式で恒等写像が一段に収まらない。

:::

:::proposition "htt_5_3_4_4" (lean := "CategoryTheory.IsFinitelyPresentable, CategoryTheory.isFinitelyPresentable_iff_preservesFilteredColimits")
*HTT 注意 5.3.4.4*　通常の圏における有限表示対象の用語（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=414)）。対応表の状態：Mathlib にある。

*主張*　$`\operatorname{Hom}(C,-)` が filtered 余極限を保つ対象は、文献によって有限表示対象と呼ばれる。

仮定：通常の局所小圏 C と対象 X（HTT と一致）。結論：有限表示対象を Hom(X,−) の filtered 余極限保存で特徴づける（一致）。この項目は通常の圏の用語であり、神経への比較は必要としない。

この用語は有限表示代数の例に対応する。HTT の compact という呼称も同じ保存条件を指し、ここでの文献による名称の違いを押さえる。

:::

:::definition "htt_5_3_4_5" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.PreservesKappaFilteredColimits, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsCompact, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityDiagram")
*HTT 定義 5.3.4.5*　κ 連続関手と κ コンパクト対象の定義（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=414)）。対応表の状態：本体にある。

*主張*　$`\kappa`-連続な関手は小さい $`\kappa`-filtered 余極限を保ち、対象は余表現関手が、左ファイブレーションは分類関手が $`\kappa`-連続なとき $`\kappa`-コンパクトである。

仮定：正則 κ、準圏と空間値の分類関手（HTT と一致）。結論：κ-filtered な全小準圏上の指定余極限の保存、共変 Hom による対象の κ-compact 性、ℵ₀ の compact 性を定義する（一致）。左ファイブレーションについては同じ分類関手の保存条件を使う。

対象の場合は各試験対象への写像空間を見る。完全コンパクト性とは異なり、保存の試験を $`\kappa`-filtered な形だけに限り、$`\kappa=\omega` を単にコンパクトと呼ぶ。

:::

:::definition "htt_5_3_4_6" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.kappaCompactObjects, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.kappaCompactInclusion")
*HTT 記法 5.3.4.6*　κ コンパクト対象の全部分準圏（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=414)）。対応表の状態：本体にある。

*主張*　$`\mathcal C^\kappa` は $`\mathcal C` の $`\kappa`-コンパクト対象が張る充満部分圏である。

仮定：準圏 C と正則 κ（HTT と一致）。結論：κ-compact 頂点が張る全部分単体集合とその包含を与える（一致）。単なる頂点集合でなく高次単体を保つ。

選ぶのは対象だけで、それらの間の写像空間は元の圏から引き継ぐ。

:::

:::lemma_ "htt_5_3_4_7" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.preservesKappaFilteredColimits_limitFamily_apex_of_small")
*HTT 補題 5.3.4.7*　κ 連続な空間値関手の小極限閉性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=414)）。対応表の状態：一部（special）。

*主張*　小さい $`\kappa`-filtered 余極限を持つ圏から空間への $`\kappa`-連続関手は、関手圏の $`\kappa`-小極限で閉じている。

KB-W2原文・型再照合：仮定：正則 κ が非可算、極限形状 K が κ-small な準圏（Lean が強い：任意の κ-small 単体集合形状を扱わない）。結論：各脚が κ-連続な元の全極限錐族の頂点関手も κ-連続（この形状の場合に一致）。各頂点で極限という hF は元の極限の指定であり、結論と別の比較写像を仮定しない。

関手圏の極限を点ごとに計算し、値域で $`\kappa`-小極限と $`\kappa`-filtered 余極限を交換する。この交換により極限関手にも保存性が移る。

:::

:::lemma_ "htt_5_3_4_8" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.covariantRepresentableInfinity_cosliceIso, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftClassification_baseChange_preservesKappaFilteredColimits, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.PreservesKappaFilteredColimits.of_functorIso")
*HTT 補題 5.3.4.8*　コンパクト左ファイブレーションの基本性質（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=414)）。対応表の状態：一部（component）。

*主張*　対象の $`\kappa`-コンパクト性はその下の左ファイブレーションの $`\kappa`-コンパクト性に等しく、$`\kappa`-連続関手による引き戻しと共変模型の $`\kappa`-小ホモトピー極限がこの性質を保つ。

KB-W2原文・型再照合：仮定：準圏、正則 κ、左ファイブレーションと κ-連続な基底変換（HTT と一致）。結論：(1) 対象の compact 性とその余スライスの分類関手の compact 性、(2) κ-連続な基底変換による保存を与える（一致）。(3) の共変モデル構造の κ-small ホモトピー極限での閉性は含まない。

左ファイブレーションを空間値関手で読むと、引き戻しは前合成に対応する。極限は分類関手の小極限に対応するので、$`\kappa`-連続関手の閉性を使える。

:::

:::lemma_ "htt_5_3_4_9" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.isKappaCompact_functorVertex_of_endFamily") (uses := "htt_1_1_2_4, htt_5_3_1_7, htt_5_3_4_5")
*HTT 補題 5.3.4.9*　コンパクトな両端を持つ射のコンパクト性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=415)）。対応表の状態：一部（stronger-hyp）。

*主張*　小さい $`\kappa`-filtered 余極限を持つ ∞ 圏では、両端が $`\kappa`-コンパクトな辺は矢印 ∞ 圏の $`\kappa`-コンパクト対象である。

K=Δ¹に限定しκを非可算、Cを全小余完備とし、同じFの全Homを表すtwisted-arrow end極限錐族Eと係数・頂点の自然な比較hr,haを追加すると、isKappaCompact\_functorVertex\_of\_endFamilyは同じF自身のκ-compact性を直接返す。Eと比較の存在を原文の仮定だけから供給したとは数えない。

矢印間の写像空間は、両端における写像空間とその可換性から組み立てる。両端の保存性を、必要な小極限と交換する。

:::

:::proposition "htt_5_3_4_13" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.isKappaCompact_functorVertex_of_endFamily") (uses := "htt_1_1_2_4, htt_5_1_2_2, htt_5_3_1_7, htt_5_3_4_5, htt_5_3_4_9, htt_5_4_5_7")
*HTT 命題 5.3.4.13*　関手の点ごとのコンパクト性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=417)）。対応表の状態：一部（stronger-hyp）。

*主張*　小さい $`\kappa`-filtered 余極限を持つ圏において、$`\kappa`-小形の図式の各頂点が $`\kappa`-コンパクトなら、その図式自体が関手圏で $`\kappa`-コンパクトである。

κ-smallな準圏Kに限定しκを非可算、Cを全小余完備とし、同じFの全Homを表すtwisted-arrow end極限錐族Eと係数・頂点の自然な比較hr,haを追加すると、isKappaCompact\_functorVertex\_of\_endFamilyは同じF自身のκ-compact性を直接返す。Eと比較の存在を原文の仮定だけから供給したとは数えない。

写像空間を検査するときは、頂点での像だけでなく図式全体の整合性が入る。形の $`\kappa`-小性により、その整合性を決める極限を filtered 余極限と交換できる。

:::

:::corollary "htt_5_3_4_14" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.covariantRepresentableInfinity_cosliceIso, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.PreservesKappaFilteredColimits.of_functorIso") (uses := "htt_1_1_2_4, htt_2_0_0_3, htt_5_3_1_7, htt_5_3_4_5")
*HTT 系 5.3.4.14*　小図式の余スライスのコンパクト性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=419)）。対応表の状態：一部（special）。

*主張*　$`\kappa`-小図式 $`p` の各頂点が $`\kappa`-コンパクトなら、その余錐の左ファイブレーション $`\mathcal C_{p/}\to\mathcal C` は $`\kappa`-コンパクトである。

KB-W2原文・型再照合：仮定：κ-compact な対象 x の一点図式 Δ⁰→C（Lean が強い：任意の κ-small 図式でなく一点形状）。結論：同じ元の余スライス Cx/→C が κ-compact（この場合に一致）。元の全分類関手との自然同型と保存性の同型不変性による。一般の図式の余スライスの比較は含まない。

分類関手の値は固定図式から各頂点への余錐空間である。これは関手圏で図式 $`p` から定値図式への写像を取ることで検査できる。

:::

:::corollary "htt_5_3_4_15" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.isKappaCompact_finiteColimit, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.isKappaCompact_smallQuasicategoryColimit_universe") (uses := "htt_1_1_2_4, htt_5_3_1_7, htt_5_3_4_5, htt_5_3_4_14")
*HTT 系 5.3.4.15*　コンパクト対象の小余極限閉性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=419)）。対応表の状態：一部（special）。

*主張*　小さい $`\kappa`-filtered 余極限を持つ圏の $`\kappa`-コンパクト対象は、元の圏で存在する $`\kappa`-小余極限で閉じている。

KB-W2原文・型再照合：仮定：正則 κ、既存の余極限と各頂点の κ-compact 性（Lean が強い：形状は有限単体集合、または非可算 κ の κ-small 準圏）。結論：同じ指定余極限頂点が κ-compact（これらの場合に一致）。有限形状は任意の有限単体集合を含み、一般 κ-small 単体集合への拡張は主張しない。

余極限対象からの写像空間は各成分からの写像空間の極限になる。その極限が $`\kappa`-小なので、元の各対象のコンパクト性をまとめられる。

:::

:::proposition "htt_5_3_4_16" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.of_retract")
*HTT 注意 5.3.4.16*　コンパクト対象のレトラクト閉性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=419)）。対応表の状態：本体にある。

*主張*　$`\kappa`-コンパクト対象はレトラクトで閉じている。

仮定：正則 κ と準圏 C、κ-compact な y のホモトピー圏内の retract x（HTT と一致。Lean は C の余極限存在を不要とする）。結論：元の x も κ-compact（一致）。共変 Hom の全自然 retract を通し、高次 Hom を捨てない。

レトラクトを余表現関手に移し、その余極限の保存性を比較のレトラクトとして読む。大きい側で比較が同値なら小さい側でも同値になる。

:::

:::proposition "htt_5_3_4_17" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.representablePresheafInfinity_isKappaCompact, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.isKappaCompact_finiteColimit, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.of_retract") (uses := "htt_1_1_2_4, htt_4_2_3_11, htt_5_1_5_3, htt_5_1_6_8, htt_5_3_4_5, htt_5_3_4_15, htt_5_3_4_16")
*HTT 命題 5.3.4.17*　コンパクト前層と小余極限のレトラクト（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=420)）。対応表の状態：一部（special）。

*主張*　小さい $`\mathcal C` の前層が $`\kappa`-コンパクトであることは、$`\kappa`-小図式で表現可能前層を余極限した対象のレトラクトであることと同値である。

KB-W2原文・型再照合：仮定：正則 κ、小準圏 C と表現可能前層の有限形状余極限の retract X（Lean が強い：κ-small 形状を有限形状に限定）。結論：同じ X が κ-compact（この場合の (1)⇒(2) と一致）。各表現可能頂点、同じ指定余極限、その retract の三宣言を直接適用する。逆方向と一般 κ-small 形状の表示は含まない。

表現可能前層から小余極限を作り、さらにレトラクトを許す。完全コンパクト性の判定よりも前層の構成に許す図式が広い。

:::

# 5.3.5 Ind-Objects

%%%
number := false
tag := "htt-5-3-5"
%%%

:::definition "htt_5_3_5_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.isIndVertex_functorVertex_iff")
*HTT 定義 5.3.5.1*　Ind 対象とフィルターな元の圏（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=421)）。対応表の状態：本体にある。

*主張*　$`\operatorname{Ind}_\kappa(\mathcal C)` は、分類される右ファイブレーションの全空間が $`\kappa`-filtered である空間値前層の充満部分圏である。

仮定：小準圏 C と正則 κ（HTT と一致）。結論：元の前層の全部分準圏である Indκ と、同じ前層を分類する右ファイブレーションの全空間の κ-filtered 性が同値（一致）。最小閉包という別の定義だけでなく、right unstraightening との比較も証明されている。

ここでは値の空間の filtered 性を各点で要求するのではない。右ファイブレーションの全空間を添字圏として見ることが定義の特徴である。

:::

:::proposition "htt_5_3_5_2" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda_inclusion")
*HTT 注意 5.3.5.2*　米田埋め込みの Ind への因子化（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=421)）。対応表の状態：本体にある。

*主張*　小さい $`\mathcal C` の Yoneda 埋め込みは $`\operatorname{Ind}_\kappa(\mathcal C)` を経由する。

仮定：小準圏 C と正則 κ（HTT と一致）。結論：元の Yoneda 関手が同じ Indκ へ全単体で因子化し、前層への包含との合成が元の関手に厳密に等しい（一致）。

表現可能前層に対応する右ファイブレーションは対象へのスライスである。そこでは恒等射が終対象なので、全空間が $`\kappa`-filtered になる。

:::

:::proposition "htt_5_3_5_3" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.isIndVertex_kappaColimitClosed, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.ind_isColimit_iff_inclusion")
*HTT 命題 5.3.5.3*　Ind のフィルター余極限閉性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=421)）。対応表の状態：本体にある。

*主張*　$`\operatorname{Ind}_\kappa(\mathcal C)` は空間値前層 ∞ 圏の $`\kappa`-filtered 余極限で閉じている。

仮定：小準圏 C と正則 κ、元の κ-filtered な小図式（HTT と一致）。結論：前層内でのその余極限は Indκ に属し、Ind の同じ余極限は包含で保存・検出される（一致）。

前層側で余極限を先に作っても、その前層を分類する右ファイブレーションには定義の filtered 性が残る。

:::

:::corollary "htt_5_3_5_4" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.isIndVertex_iff_singleFilteredPresentation, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.isIndVertex_functorVertex_iff") (uses := "htt_1_1_2_4, htt_5_1_2_2, htt_5_1_3_2, htt_5_1_5_2, htt_5_1_5_3, htt_5_3_1_7, htt_5_3_3_3, htt_5_3_5_2, htt_5_3_5_3")
*HTT 系 5.3.5.4*　Ind の単一フィルター表示による特徴づけ（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=422)）。対応表の状態：一部（component）。

*主張*　前層が $`\operatorname{Ind}_\kappa(\mathcal C)` に属することは表現可能前層の小さい $`\kappa`-filtered 余極限であることと同値で、$`\mathcal C` が $`\kappa`-小余極限を持つなら $`\kappa`-小極限の保存とも同値である。

KB-W2原文・型再照合：仮定：小準圏 C、正則 κ、前層 F（HTT と一致）。結論：(1) 元の表現可能前層の単一 κ-filtered 余極限表示と (2) Indκ 所属が同値（一致）。C が κ-small 余極限を持つ場合の (3) κ-small 極限保存との同値は含まない。

第三の判定は前層の反変性に注意して読む。始域 $`\mathcal C^{\mathrm{op}}` における極限は、$`\mathcal C` の余極限を反転したものである。

:::

:::proposition "htt_5_3_5_5" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.indYoneda_isKappaCompact")
*HTT 命題 5.3.5.5*　Ind の米田像のコンパクト性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=422)）。対応表の状態：本体にある。

*主張*　元の各対象の Yoneda 像は $`\operatorname{Ind}_\kappa(\mathcal C)` における $`\kappa`-コンパクト対象である。

仮定：小準圏 C、正則 κ、C の対象 x（HTT と一致）。結論：元の Indκ 内の元の米田像が κ-compact（一致）。前層内だけでなく Ind の共変 Hom の全小 filtered 余極限保存を結論する。

表現可能前層からの写像は評価であり、前層側で計算する $`\kappa`-filtered 余極限と可換する。

:::

:::lemma_ "htt_5_3_5_8" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.ind_exists_leftKanExtension, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indContinuous_isLeftKanExtension, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indLeftKanExtension_preservesSmallKappaFilteredColimits")
*HTT 補題 5.3.5.8*　Ind からの左 Kan 延長と連続性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=423)）。対応表の状態：本体にある。

*主張*　標的に小さい $`\kappa`-filtered 余極限があれば、Yoneda の本質像上の関手は Ind へ左 Kan 拡張でき、Ind からの関手がそのような拡張であることは $`\kappa`-連続性と同値である。

仮定：小準圏 C、正則 κ、κ-filtered な小余極限を持つ準圏 D（HTT と一致。充満な米田像 C₀ の代わりにその同値な模型 C を使う）。結論：任意の C→D の左 Kan 延長の存在、および同じ延長の κ-連続性との同値（一致）。任意の指定単位を持つ左 Kan 延長について保存を結論する。

元の対象への値を指定し、その filtered 余極限への値を保存性から定める。点ごとの左 Kan 拡張の計算が、この規則を関手としてまとめる。

:::

:::proposition "htt_5_3_5_9" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.ind_exists_leftKanExtension, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indContinuous_isLeftKanExtension, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indLeftKanExtension_preservesSmallKappaFilteredColimits") (uses := "htt_1_1_2_4, htt_5_1_5_5, htt_5_3_1_7, htt_5_3_5_8")
*HTT 注意 5.3.5.9*　余極限のクラスごとの自由完備化の原理（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=424)）。対応表の状態：一部（special）。

*主張*　前層圏内で表現可能前層を指定種の余極限で閉じた部分圏では、その種の余極限を保つ関手を表現可能対象上からの左 Kan 拡張として扱う方法がある。

KB-W2原文・型再照合：仮定：余極限のクラスを κ-filtered な小形状に固定する（Lean が強い：任意のクラス S ではない）。結論：その閉包 Indκ からの左 Kan 延長の存在と、そのクラスの余極限保存による特徴づけ（この場合に一致）。一般の閉包への構成を主張しない。

全小余極限の場合は前層圏、$`\kappa`-filtered の場合は Ind の結果が対応する。次節ではこの方法を余極限の形を指定した構成に使う。

:::

:::proposition "htt_5_3_5_10" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indKappaContinuousRestriction_isQCatEquivalence, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indKappaContinuousRestrictionEquivalence_hom")
*HTT 命題 5.3.5.10*　Ind の自由フィルター完備化の普遍性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=424)）。対応表の状態：本体にある。

*主張*　小さい $`\mathcal C` と小さい $`\kappa`-filtered 余極限を持つ $`\mathcal D` について、Yoneda への制限は $`\kappa`-連続関手 $`\operatorname{Ind}_\kappa(\mathcal C)\to\mathcal D` の ∞ 圏と $`\operatorname{Fun}(\mathcal C,\mathcal D)` の同値を与える。

仮定：小準圏 C、正則 κ、κ-filtered な小余極限を持つ準圏 D（HTT と一致）。結論：元の米田関手への実際の制限 Funκ(Indκ(C),D)→Fun(C,D) が全準圏同値（一致）。対象や関手の core だけでなく非可逆自然変換と全高次単体を扱う。

関手の延長の存在だけでなく、自然変換と高次の比較も元の圏への制限で回復する。これが Ind の普遍性になる。

:::

:::proposition "htt_5_3_5_11" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indComparison_isFullyFaithful_of_compact, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indComparison_isQCatEquivalence") (uses := "htt_1_1_2_4, htt_4_2_3_11, htt_5_1_3_1, htt_5_1_3_2, htt_5_3_1_7, htt_5_3_4_5, htt_5_3_5_4, htt_5_3_5_5")
*HTT 命題 5.3.5.11*　Ind からの関手の充満忠実性と同値判定（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=425)）。対応表の状態：一部（component）。

*主張*　Ind からの $`\kappa`-連続関手は、その Yoneda への制限が充満忠実で像が $`\kappa`-コンパクトなら充満忠実であり、さらに像が標的を $`\kappa`-filtered 余極限で生成すると同値になる。

KB-W2原文・型再照合：仮定：小準圏 C と正則 κ、元の κ-連続 F、Fj が充満忠実で像が κ-compact（HTT と一致）。結論：(1) F が充満忠実、一方 κ-filtered な表示で D を生成すれば F は同値（(2) の十分性と一致）。F の同値から三条件を回収する必要性まで一つの同値として宣言されていないため、ここでは十分性だけを採用する。

写像空間の比較を元の小さい圏で調べ、コンパクト性を使って Ind の対象まで広げる。本質的全射性に必要なのは、標的のすべてが指定した生成対象から得られることである。

:::

:::proposition "htt_5_3_5_12" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.presheaf_isKappaAccessible_aleph0, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsKappaAccessible.exists_smallCompactModel, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsKappaAccessible.compactModel_isKappaCompactGenerating, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indComparison_isQCatEquivalence, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsKappaAccessible.of_cardinalChangeBound, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.cardinalChangeBound_aleph0")
*HTT 命題 5.3.5.12*　コンパクト前層の小ささと Ind 表示（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=426)）。対応表の状態：本体にある。

*主張*　小さい $`\mathcal C` の前層圏の $`\kappa`-コンパクト対象の圏は本質的小さく、その小さい模型 $`\mathcal D` の $`\operatorname{Ind}_\kappa(\mathcal D)` は元の前層圏と同値である。

仮定：小準圏 C と任意の正則 κ（HTT と一致）。結論：全 κ-compact 前層の全部分準圏に小模型 D があり、同じ包含を米田上で回収する任意の κ-連続な比較 Indκ(D)→P(C) が同値（一致）。κ=ℵ₀ は構成済みの前層の accessibility、κ\>ℵ₀ は cardinalChangeBound\_aleph0 を of\_cardinalChangeBound に適用して供給するため、濃度変更を追加仮定に残さない。全 compact 模型の生成性を同じ比較の同値判定へ直接渡す。

コンパクトな前層を小さい範囲にまとめた後、$`\kappa`-filtered 余極限を自由に加える。こうして元の大きい前層圏を小さい部分から回復する。

:::

:::proposition "htt_5_3_5_14" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda_finiteColimit_isColimit")
*HTT 命題 5.3.5.14*　Ind の米田関手の小余極限保存（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=427)）。対応表の状態：一部（stronger-hyp）。

*主張*　$`\mathcal C\to\operatorname{Ind}_\kappa(\mathcal C)` の Yoneda 埋め込みは $`\mathcal C` に存在する $`\kappa`-小余極限を保つ。

原文のκ-small図式を有限形状に限定し、さらにIndFiniteLimitExchangeInput（全有限形状でのcoherent filtered極限交換）を明示入力すると、同じindYonedaの有限余極限保存が直接得られる。一般κ-small形状は扱わず、この交換入力の実在を本行の型が証明したとはしない。

比較の標的を前層全体ではなく Ind に制限する。コンパクトな源の指定余極限を、Ind の試験対象に対する写像空間で検査する。

:::

:::proposition "htt_5_3_5_15" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indFinitePoset_has_singleFilteredDiagramPresentation")
*HTT 命題 5.3.5.15*　有限半順序図式と Ind の交換（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=428)）。対応表の状態：一部（component）。

*主張*　小さい $`\mathcal C` と有限半順序集合 $`A` について、$`\operatorname{Ind}_\kappa(\operatorname{Fun}(N(A),\mathcal C))\simeq\operatorname{Fun}(N(A),\operatorname{Ind}_\kappa(\mathcal C))` である。

KB-W2原文・型再照合：仮定：小準圏 C、正則 κ、有限半順序 P と N(P)→Indκ(C) の図式（HTT と一致）。結論：同じ全図式自身が、小さい単一 κ-filtered な C 内の全図式の米田像の余極限表示を持つ（一致）。比較 Indκ(Fun(N(P),C))→Fun(N(P),Indκ(C)) の充満忠実性や準圏同値までは含まない。

各頂点だけを独立に filtered 余極限で書くのではなく、有限な図式の全体を $`\mathcal C` 値図式の filtered 余極限として書く。

:::

# 5.3.6 Adjoining Colimits to ∞-Categories

%%%
number := false
tag := "htt-5-3-6"
%%%

:::definition "htt_5_3_6_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.KappaContinuousFunctorInfinity") (uses := "htt_1_1_2_4, htt_1_2_13_4")
*HTT 記法 5.3.6.1*　指定余極限を保つ関手の全部分準圏（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=430)）。対応表の状態：一部（special）。

*主張*　$`\operatorname{Fun}_{\mathcal R}(\mathcal C,\mathcal D)` は指定余錐の族 $`\mathcal R` を余極限に送る関手の充満部分圏で、形の族 $`\mathcal K` に対しては $`\mathcal K`-型余極限を持つことと保つことを定める。

KB-W2原文・型再照合：仮定：形状のクラス K を κ-filtered な全小準圏に固定する（Lean が強い）。結論：同じ全関手準圏で K-余極限保存関手の張る全部分準圏 FunK を定義する（一致）。任意の指定された余極限図式族 R の FunR までは定義しない。

余錐の指定と、すべての図式に対する形の指定を分ける。指定余錐をすでに余極限だと仮定しない定式化もここでは許される。

:::

:::proposition "htt_5_3_6_2" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.ind_exists_colimitCone, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indKappaContinuousRestriction_isQCatEquivalence, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda_isFullyFaithful") (uses := "htt_1_1_2_4, htt_1_2_13_4")
*HTT 命題 5.3.6.2*　関係を課した自由余極限完備化（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=430)）。対応表の状態：一部（special）。

*主張*　形の族 $`\mathcal K` の余極限を自由に備え、指定した $`\mathcal R` の余錐を余極限にする普遍圏があり、$`\mathcal R` がすべてもともと余極限なら元の圏からの関手は充満忠実である。

KB-W2原文・型再照合：仮定：C は小準圏、R は空、K は κ-filtered な全小準圏（Lean が強い：任意の関係・形状族ではない）。結論：Indκ は K-余極限を持ち、同じ米田制限による全関手準圏の普遍同値と j の充満忠実性を満たす（この場合に (1)〜(3) と一致）。

この普遍圏からの余極限保存関手を指定することは、元の圏から指定余錐を余極限に送る関手を指定することと同じになる。

:::

:::proposition "htt_5_3_6_4" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.presheaf_densityImages_canonicalColimits, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCanonical_pinchedHomMap_equivalence")
*HTT 例 5.3.6.4*　前層圏としての自由余完備化（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=431)）。対応表の状態：一部（component）。

*主張*　小さい $`\mathcal C` で指定余錐を空、形を全小単体的集合とすると、普遍構成は Yoneda $`\mathcal C\to\mathcal P(\mathcal C)` になる。

KB-W2原文・型再照合：仮定：小準圏 C と小余完備 D、P(C)→D の小余極限保存関手（Lean が強い：C は任意の単体集合でなく準圏）。結論：同じ米田制限が保存関手間の全写像空間で同値となる（普遍性の充満忠実性と一致）。全制限射の本質的全射性を含む同値までの証明はない。

追加で保存すべき余錐を課さず、小余極限すべてを自由に加える場合である。

:::

:::proposition "htt_5_3_6_7" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indKappaContinuousRestriction_isQCatEquivalence, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.ind_exists_colimitCone, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda_isFullyFaithful")
*HTT 例 5.3.6.7*　自由フィルター完備化としての Ind（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=433)）。対応表の状態：本体にある。

*主張*　小さい $`\mathcal C` に対し、指定余錐を課さず小さい $`\kappa`-filtered 形だけを自由に加える普遍圏は $`\operatorname{Ind}_\kappa(\mathcal C)` である。

仮定：小準圏 C、K 空、K′ は小 κ-filtered 形状（HTT と一致）。結論：元の Indκ は全 K′-余極限を持ち、元の米田関手が充満忠実でその制限が全準圏同値となる（一致）。抽象 PK′K の別実装を要求せず、原典でそれを特徴づける普遍性そのものを確認した。

前層全体のうち、表現可能前層から filtered 余極限で作れる範囲を選ぶ。この制限が、対応する余極限保存関手の普遍性と一致する。

:::

:::proposition "htt_5_3_6_9" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemYoneda_pre_isQCatEquivalence, SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemYoneda_isIdempotentCompletion")
*HTT 例 5.3.6.9*　Idem 余極限の自由付加と冪等完備化（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=433)）。対応表の状態：一部（special）。

*主張*　指定余錐を課さず $`\mathrm{Idem}` 型余極限だけを自由に加える普遍圏は冪等完備化である。

KB-W2原文・型再照合：仮定：小準圏 C と冪等完備な準圏 E（Lean が強い：任意の大きさの C に対する別宇宙の構成はこの宣言で述べない）。結論：Idem(C) は同じ Yoneda の冪等完備化で、制限 Fun(Idem(C),E)→Fun(C,E) が全準圏同値（この場合の自由冪等完備化の普遍性と一致）。

$`\mathrm{Idem}` 型の余極限が既存の冪等辺を分裂させるので、この形だけの余極限の追加が冪等完備化を与える。

:::

