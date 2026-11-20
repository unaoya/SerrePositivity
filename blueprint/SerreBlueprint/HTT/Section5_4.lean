-- audit2: 7d0968dad3e8672a6213dc0e508983c17f14eaaa inputs sha256 b3e2631992a041109ef8ab3a4836cc24453830556fb4a9c55f9a166f68e2cde1
-- audit2 baselines: 23cbebdfe9d75717f3f248bb0069ebd9dc9bbef6, cddf4d2dac6a409e64204686cf743e703350a6f6
import Verso
import VersoManual
import VersoBlueprint
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.InitialSectionLifting
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PullbackInitialVertices
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.Accessibility
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.Accessible
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AccessibleEquivalence
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AccessibleFunctor
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AccessibleIndRepresentation
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.SmallSourceCosliceCompactness
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.SmallFilteredPieces
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IndComplete
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.PullbackFilteredColimits
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.SmallSpaceCompact
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.SpacePresentable
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.CompactIndCompletion
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.FilteredRetraction
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndAccessible
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndRestrictionEquivalence
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CardinalChangeBound
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CompactEquivalence
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CompactModelGenerators
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FiniteSpacePresentation
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FunctorPresentable
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ImageCompactGenerators
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IndCardinalChange
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.NativeAdjointFunctorCriterion
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PiPresentable
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresheafPresentable
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PullbackCompactObjects
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PullbackCosliceBaseChange
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallCompactModels
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SourceCosliceFilteredColimits
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.QCatPullbackLimit
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.LeftAdjointAllColimitPreservation
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.LimitProjectionExistence
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.PullbackSmallColimits
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.TrivialFibrationEquivalence
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.SlicePostcompEquivalenceLifting
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.LocallySmall
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.ColimitCoconeProjection
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.Terminal
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TerminalVertices
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CompletenessEquivalence

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "HTT 5.4 Accessible ∞-Categories" =>
%%%
number := false
tag := "htt-5-4"
%%%

HTT 5.4 の項目のうち、本体か Mathlib に対応があるもの（対応表 `research/htt-coverage` の状態が「なし」でないもの）。本文は日本語で独立に書いた要約と解説で、原典の本文の写しではない。

# 5.4.1 Locally Small ∞-Categories

%%%
number := false
tag := "htt-5-4-1"
%%%

:::corollary "htt_5_4_1_5" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.smallKanObject_isKappaCompact")
*HTT 系 5.4.1.5*　空間の本質的小性とコンパクト性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=439)）。対応表の状態：一部（special）。

*主張*　非可算正則基数 $`\kappa` に対し、空間の $`\kappa`-コンパクト性は全基点・全次数のホモトピー集合の $`\kappa`-小性と同値であり、最小模型や弱同値な模型の小性によっても判定できる。

KB-W2原文・型再照合：仮定：非可算正則 κ、κ-small な Kan 模型 K（Lean が強い：同値前の一般の X ではなく (3) の模型自身）。結論：その同じ空間頂点が κ-compact（(3)⇒(5) のこの場合に一致）。ホモトピー群の濃度、minimal 模型、compact 性から小模型を回収する方向は含まない。

この判定には連結成分の個数も含む。同じ条件は、最小 Kan 模型の $`\kappa`-小性、$`\kappa`-小な Kan 複体からのホモトピー同値、$`\kappa`-小な単体集合からの弱ホモトピー同値でも表せる。原典の (6) は単に本質的に小さいと書くが、証明が使う 5.4.1.2 の濃度条件に合わせ、本質的に $`\kappa`-小さいと読む。

:::

:::proposition "htt_5_4_1_6" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FiniteSpacePresentation.exists_finiteSpacePresentation, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IsKappaCompact.retract_of_colimit")
*HTT 注意 5.4.1.6*　コンパクト空間の有限複体レトラクト表示（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=440)）。対応表の状態：一部（component）。

*主張*　コンパクトな空間は、非退化単体が有限個の単体集合が表す空間のホモトピー圏でのレトラクトになる。

KB-W2原文・型再照合：仮定：compact な小 Kan 空間 X（HTT と一致）。結論：元の X は有限部分複体の Kan 置換の一つの項のホモトピー圏内 retract（有限単体集合を空間として読む最初の結論と一致）。有限部分複体の元の包含から作った余錐に同じ retract 判定を適用する。単連結の場合の有限模型との同値や Wall の障害による判定は含まない。

$`\kappa=\omega` では有限模型そのものとの弱同値は一般には得られない。連結かつ単連結な場合や Wall の有限性障害が消える場合には有限模型との弱同値まで取れる。

:::

:::proposition "htt_5_4_1_8" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.presheaf_isPresentable, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsPresentable.isLocallySmall")
*HTT 例 5.4.1.8*　前層準圏の局所小性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=441)）。対応表の状態：一部（component）。

*主張*　$`C` が局所小、$`D` が本質的に小なら、関手圏 $`\operatorname{Fun}(D,C)` は局所小である。

KB-W2原文・型再照合：仮定：小準圏 D（HTT と一致）。結論：P(D) の局所小性（原典の最終文と一致）。一般の C,D についての冒頭の「CD is essentially small」は C=Set,D=Δ⁰ で成り立たず、証明末尾は locally small を述べる（source-notes 参照）。この候補はその冒頭の誤記を正しいとするものではない。

有限個の関手の像を同時に含む小さい充満部分圏を $`C` の中に取れば、関手間の写像空間の小性をそこで判定できる。原典の冒頭は「本質的に小」と印刷されているが、後続の証明と前層圏の例が示す結論は局所小性である。実際、$`D=\Delta^0` なら関手圏は $`C` 自身になる。

:::

# 5.4.2 Accessibility

%%%
number := false
tag := "htt-5-4-2"
%%%

:::definition "htt_5_4_2_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessible, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.isKappaAccessible_iff_indEquivalence")
*HTT 定義 5.4.2.1*　到達可能準圏の Ind 表示による定義（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=441)）。対応表の状態：本体にある。

*主張*　小さい ∞ 圏の $`\operatorname{Ind}_\kappa` 完備化と同値な ∞ 圏を $`\kappa`-可到達と呼び、ある正則基数でこの条件を満たす圏を可到達と呼ぶ。

仮定：準圏 C と正則 κ（HTT と一致）。結論：κ-accessible であることと小準圏 A による Indκ(A)≃C の存在が同値、およびある正則 κ の存在による accessible 性（一致）。単なる生成性の定義だけでなく実際の Ind 比較を使う。

可到達性は、小さい生成圏から指定の濾過余極限を加えることで圏全体を復元できることを表す。

:::

:::proposition "htt_5_4_2_2" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.isKappaAccessible_iff_indEquivalence, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsAccessible.isLocallySmall, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsKappaAccessible.exists_smallCompactModel, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsKappaAccessible.compactModel_isKappaCompactGenerating, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaCompactGenerating")
*HTT 命題 5.4.2.2*　到達可能性のコンパクト生成による判定（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=441)）。対応表の状態：本体にある。

*主張*　$`\kappa`-可到達性は、小さい $`\kappa`-濾過余極限が存在し、本質的に小さい $`\kappa`-コンパクト対象の充満部分圏がそれらの余極限で全体を生成することと同値である。

仮定：準圏 C と正則 κ（HTT と一致）。結論：Ind 表示と、小さい compact 全部分生成圏・全小 κ-filtered 余極限存在の条件が同値であり、局所小性および全 compact 部分の小模型とその生成性も得られる（一致）。本質的小部分はその小同値模型で記述する。

生成部分圏には、コンパクト対象をすべて集めて用いても、十分な本質的小部分圏を選んでもよい。全コンパクト対象を使う定式化には全体の局所小性も明示されている。

:::

:::lemma_ "htt_5_4_2_4" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.compactIndYoneda_isIdempotentCompletion, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indInfinity_isKappaAccessible, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsKappaAccessible.exists_smallCompactModel")
*HTT 補題 5.4.2.4*　Ind のコンパクト部分による冪等完備化（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=442)）。対応表の状態：本体にある。

*主張*　小さい ∞ 圏 $`C` の米田埋め込みは、$`\operatorname{Ind}_\kappa(C)` 内の $`\kappa`-コンパクト対象の充満部分圏を $`C` の冪等完備化として表示する。

仮定：小準圏 C、正則 κ（HTT と一致）。結論：元の米田関手 C→(Indκ C)κ が冪等完備化であり、その全 compact 部分に小模型が存在する（一致）。Ind 全体を小さいと取り違えていない。

コンパクト対象は、米田像の濾過余極限として書くと恒等射がある段階を経由するため、米田像のレトラクトになる。この部分圏は本質的に小さい。

:::

:::definition "htt_5_4_2_5" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessibleFunctor, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor.of_le")
*HTT 定義 5.4.2.5*　到達可能関手と濃度を増やした連続性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=443)）。対応表の状態：本体にある。

*主張*　可到達な圏を始域とする関手が可到達であるとは、ある正則基数 $`\kappa` に対して小さい $`\kappa`-濾過余極限を保つことである。

仮定：accessible な始域と正則 κ（HTT と一致。Lean の述語形成には始域の accessibility 自体を要求しない）。結論：ある κ の filtered 余極限保存による accessible 関手の定義と、それ以上の正則濃度での保存（一致）。

いったんこの性質を持てば、さらに大きな正則基数で濾過性を課した図式についても保存が従う。

:::

:::proposition "htt_5_4_2_6" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessibleFunctor")
*HTT 注意 5.4.2.6*　標的の到達可能性を仮定しない用語（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=443)）。対応表の状態：本体にある。

*主張*　可到達関手という用語は通常、始域・終域とも可到達の場合に使うが、終域の可到達性をまだ仮定していない場合にも使える。

仮定：accessible な C と任意の準圏 C′ への関手（HTT と一致）。結論：標的 C′ の accessibility を仮定せず、正則濃度での filtered 余極限保存を述べられる（一致）。

定義で検査するのは指定の余極限の保存である。終域全体が小さい生成系を持つかどうかは別の問いである。

:::

:::proposition "htt_5_4_2_7" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.space_isKappaAccessible_aleph0, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.presheaf_isKappaAccessible_aleph0")
*HTT 例 5.4.2.7*　空間と前層準圏の到達可能性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=443)）。対応表の状態：本体にある。

*主張*　空間の ∞ 圏および任意の小さい ∞ 圏上の空間値前層圏は可到達である。

仮定：小準圏 C（HTT と一致）。結論：空間準圏と P(C) は ℵ₀-accessible、従って accessible（一致）。個々の前層の生成性を仮定せず構成する。

前層をコンパクトな前層の濾過余極限で生成する表示を使う。空間の圏は、始域を一点とした場合に当たる。

:::

:::lemma_ "htt_5_4_2_8" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.SmallFilteredPieces, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.exists_smallFilteredPiece_containing, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.smallFilteredPieces_isCardinalFiltered, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.smallFilteredPieces_cover")
*HTT 補題 5.4.2.8*　小フィルター部分半順序による被覆（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=443)）。対応表の状態：本体にある。

*主張*　$`\kappa\ll\kappa'` なら、$`\kappa'`-濾過半順序は $`\kappa'`-小な $`\kappa`-濾過部分集合の合併であり、それらの部分集合の包含順序も $`\kappa'`-濾過である。

仮定：正則 κ\<κ′、全 α\<κ,β\<κ′ について β\^α\<κ′、κ′-filtered な半順序 I（HTT と一致。Lean は I の κ-filtered 性だけで足りる）。結論：κ′-small かつ κ-filtered な部分集合の全族が κ′-filtered で、全ての元を覆い、任意の κ′-small 部分を含むものも選べる（一致）。

ここで $`\kappa\ll\kappa'` は、$`\tau_0<\kappa'` と $`\kappa_0<\kappa` に対して $`\tau_0^{\kappa_0}<\kappa'` となる条件である。小さい部分集合に必要な上界を順に加えても濃度が $`\kappa'` 未満にとどまる。

:::

:::proposition "htt_5_4_2_9" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsKappaAccessible.of_cardinalChangeBound, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsCardinalChangeBound")
*HTT 命題 5.4.2.9*　到達可能性の濃度変更（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=444)）。対応表の状態：本体にある。

*主張*　$`\kappa`-可到達な ∞ 圏は、$`\kappa\ll\kappa'` を満たす任意の正則基数 $`\kappa'` に対して $`\kappa'`-可到達でもある。

仮定：κ-accessible な C、正則 κ′\>κ と全 α\<κ,β\<κ′ に対する β\^α\<κ′（HTT と一致。Mathlib のより弱い sharplyLT と混同しない）。結論：C は同じ κ′ で accessible（一致）。

元の濾過表示を小さい部分図式に分けることで、新しい基数でコンパクトな生成対象を作る。基数の通常の大小関係だけではこの移行は保証されない。

:::

:::proposition "htt_5_4_2_11" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsKappaAccessible.exists_smallCompactModel")
*HTT 注意 5.4.2.11*　コンパクト部分準圏の本質的小性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=444)）。対応表の状態：一部（stronger-hyp）。

*主張*　可到達な ∞ 圏では、任意の正則基数 $`\kappa` について $`\kappa`-コンパクト対象の圏は本質的に小さい。

KB-W2原文・型再照合：仮定：C が κ-accessible（Lean が強い：ある濃度で accessible であるだけでなく同じ指定 κ を要求）。結論：同じ κ-compact 全部分準圏が小準圏と全同値（この場合に一致）。任意の κ に対する一般の accessibility からの回収は含まない。

与えられた基数で圏が生成されるとは限らない。可到達性を確保できる大きな基数に移し、もとのコンパクト対象をその中に含めて小性を得る。

:::

:::definition "htt_5_4_2_12" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessibleFunctor, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices")
*HTT 記法 5.4.2.12*　到達可能関手の全部分準圏の記法（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=444)）。対応表の状態：本体にある。

*主張*　可到達 ∞ 圏 $`C,D` に対し、$`\operatorname{Fun}_{\mathrm A}(C,D)` は可到達関手を対象とする関手圏の充満部分圏である。

同じFun(C,D)=(ihom C).obj DでIsAccessibleFunctorを満たす頂点が張るfullSubcomplexOnVerticesはFunA(C,D)という記法の定義そのもの。対象と全高次単体を同じ関手準圏のまま取る。

可到達性は対象となる関手に課す条件であり、それらの間の自然変換は関手圏からすべて引き継ぐ。

:::

:::proposition "htt_5_4_2_13" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_compactPreservingCardinal_of_smallFixedVertexMaps, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsKappaAccessible.exists_compactModelIndRepresentation, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indKappaContinuousRestriction_isQCatEquivalence")
*HTT 注意 5.4.2.13*　到達可能関手のコンパクト対象での決定（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=444)）。対応表の状態：一部（stronger-hyp）。

*主張*　可到達 ∞ 圏の間の可到達関手には、濾過余極限の保存とコンパクト対象の保存がともに成り立つ正則基数 $`\kappa` があり、関手は $`C^\kappa` への制限で同値まで決まる。

KB-W2原文・型再照合：仮定：accessible な二準圏と accessible 関手（Lean が強い：始域の固定頂点全写像が宇宙小である strict 条件を要求）。結論：ある大きい正則濃度 μ で関手が μ-compact 対象を保ち、全 compact 小模型からの制限が元の関手を同値を除き決める（この場合に一致）。一般の始域への strict 模型輸送をここでは追加していない。

まず余極限の保存と両圏の生成に共通の基数を選ぶ。その生成対象の像のコンパクト性を一括して抑えるよう基数を上げれば、小さい部分圏上の値から濾過余極限によって関手を再構成できる。

:::

# 5.4.3 Accessibility and Idempotent Completeness

%%%
number := false
tag := "htt-5-4-3"
%%%

:::proposition "htt_5_4_3_4" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IsKappaCompact.retract_of_colimit")
*HTT 命題 5.4.3.4*　大フィルター余極限の米田像へのレトラクト（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=448)）。対応表の状態：一部（stronger-hyp）。

*主張*　$`\kappa<\tau` を非可算正則基数とし、$`\tau`-小な ∞ 圏の写像空間が本質的に $`\kappa`-小なら、その米田像の $`\tau`-濾過図式の前層圏での余極限は一つの表現可能前層のレトラクトになる。

KB-W2原文・型再照合：仮定：τ-filtered な米田図式の指定余極限 X（Lean が強い：原典の小ささ・Hom 上界のほか X 自身が τ-compact であることを仮定）。結論：元の X が同じ米田図式の一つの項の retract（結論は一致）。compact 性を原典の濃度条件から証明したとは数えていない。

圏と写像空間に別々の大きさの仮定を置くことで、図式全体の余極限をある段階の像から分裂させる。この段階ではレトラクトの表現可能性に冪等完備性を使っていない。

:::

:::corollary "htt_5_4_3_6" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.ind_isIdempotentComplete, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible.exists_indEquivalence, SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.isIdempotentComplete_iff_of_equivalence")
*HTT 系 5.4.3.6*　小準圏の到達可能性と冪等完備性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=449)）。対応表の状態：一部（direction）。

*主張*　小さい ∞ 圏の可到達性は冪等完備性と同値であり、この条件を満たす圏から可到達 ∞ 圏への関手はすべて可到達である。

KB-W2原文・型再照合：仮定：accessible な小準圏 C（HTT と一致）。結論：C は idempotent complete（同値の必要方向と一致）。一般の accessible C の実 Ind 模型の冪等完備性を同じ全同値で戻す。小 idempotent complete C の accessibility、およびそこからの任意の関手の accessibility は含まない。

小さい圏では十分大きな基数を選べる。その基数の濾過図式の余極限を扱う際、表現可能前層のレトラクトを圏内に戻せることが冪等完備性に対応する。

:::

# 5.4.4 Accessibility of Functor ∞-Categories

%%%
number := false
tag := "htt-5-4-4"
%%%

:::proposition "htt_5_4_4_3" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functor_isPresentable") (uses := "htt_1_1_2_4, htt_5_1_2_2, htt_5_1_5_3, htt_5_3_4_13, htt_5_4_2_1, htt_5_4_2_2")
*HTT 命題 5.4.4.3*　到達可能な値を持つ関手準圏の到達可能性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=452)）。対応表の状態：一部（stronger-hyp）。

*主張*　小さい単体集合 $`K` と可到達 ∞ 圏 $`C` に対し、$`\operatorname{Fun}(K,C)` は可到達である。

KB-W2原文・型再照合：仮定：小準圏 K と presentable な C（Lean が強い：C は accessible に加えて全小余極限を持つ。K も任意の単体集合でなく準圏）。結論：元の Fun(K,C) は presentable、従って accessible（この場合に一致）。任意の accessible C や非準圏形状への比較を追加していない。

図式の添字を小さく固定すると、十分大きな共通の基数を用いて、図式圏の対象そのものを濾過余極限で生成できる。

:::

# 5.4.5 Accessibility of Undercategories

%%%
number := false
tag := "htt-5-4-5"
%%%

:::proposition "htt_5_4_5_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.isTerminalVertex_iff_trivialKanFibration, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.qCatEquivalenceOfTrivialKanFibration, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.isAccessible_iff_equivalence")
*HTT 注意 5.4.5.1*　上圏の到達可能性への双対的な案内（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=453)）。対応表の状態：一部（special）。

*主張*　小さい図式の上の錐の圏にも、下の余錐の圏と同じ可到達性の結論が成り立つ。

KB-W2原文・型再照合：仮定：accessible な C と終対象 x の一点図式（Lean が強い：任意の小図式 p ではなく終対象の一点）。結論：元の C/x は C への同じ射影が trivial Kan fibration、従って全準圏同値となるので accessible（この場合に一致）。同値模型を新しく仮定するのでなく終対象の既存判定から構成する。

下の圏の結果はこの節で先に示す。上の圏の証明は、関手圏の可到達性と可到達圏のホモトピー引き戻しの定理を用いる。引き戻しの定理の証明では先に下の圏の性質を使う。

:::

:::lemma_ "htt_5_4_5_2" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isInitialVertex_pullback_of_components")
*HTT 補題 5.4.5.2*　ホモトピー引き戻しの始対象の判定（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=453)）。対応表の状態：一部（stronger-hyp）。

*主張*　Joyal の意味のホモトピー引き戻しでは、二つの頂点の圏に始対象があり底への両関手がそれを保つなら、引き戻しにも始対象があり、始対象であることは両射影で判定できる。

KB-W2原文・型再照合：仮定：準圏の strict 引き戻しの指定頂点と、三成分の始対象性（Lean が強い：第一脚の全 pinched Hom 写像が Kan fibration という条件を明示）。結論：元の引き戻し頂点は始対象（成分の始対象性⇒始対象の方向に一致）。始対象の存在と逆方向を含む一般の iff は含まない。

始対象を両側で選ぶと共通の底で同値になるため、引き戻しの対象が得られる。普遍性は、そこからの写像空間を両成分の写像空間のホモトピー引き戻しとして判定する。

:::

:::lemma_ "htt_5_4_5_3" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.sliceUnderPostcomp_equivalenceLifting")
*HTT 補題 5.4.5.3*　圏的ファイブレーションの余スライスへの移行（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=454)）。対応表の状態：本体にある。

*主張*　圏論的ファイブレーション $`p:X\to Y` と図式 $`f:K\to X` に対し、誘導される余錐の圏の写像 $`X_{f/}\to Y_{pf/}` も圏論的ファイブレーションである。

仮定：準圏間の categorical fibration と任意の元の図式 f（HTT と一致。EquivalenceLifting は全単射 categorical equivalence に対する同じ持ち上げ条件）。結論：同じ Xf/→Ypf/ の全余スライス後合成も同じ categorical lifting を持つ（一致）。

図式の始域を固定して余錐を移す操作は、圏論的ファイブレーションの持ち上げ性と両立する。

:::

:::lemma_ "htt_5_4_5_4" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pullbackCoslice_isPullback, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.sliceUnderPostcomp_equivalenceLifting, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.qCatPullbackInfinityCone_isLimit")
*HTT 補題 5.4.5.4*　余スライスによる引き戻しの保存（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=454)）。対応表の状態：一部（special）。

*主張*　Joyal の意味のホモトピー引き戻しをなす四角形で、左上の一つの図式とその各像の余錐の圏を作ると、得られる四角形もホモトピー引き戻しになる。

KB-W2原文・型再照合：仮定：元の平方を一方が categorical fibration である strict pullback 模型で与える（Lean が強い：任意の別の homotopy Cartesian 平方を入力しない）。結論：元の全余スライス平方は strict pullback で、その同じ脚は categorical lifting を保つため対応する Cat∞ の錐も極限（この模型で一致）。

元の図式と各頂点での像を固定して、対応する下の圏を同時に取る。同値を含む整合性も新しい四角形に引き継がれる。

:::

:::lemma_ "htt_5_4_5_5" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.pullback_hasSmallColimits, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.pullback_isColimitCone_iff_components")
*HTT 補題 5.4.5.5*　引き戻しの余極限の成分判定と存在（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=454)）。対応表の状態：一部（stronger-hyp）。

*主張*　ホモトピー引き戻しの両側に $`K`-型余極限があり、底への関手が保存するなら、引き戻しにも $`K`-型余極限があり、余極限余錐は両成分で判定できる。

KB-W2原文・型再照合：仮定：一方が categorical fibration である strict pullback、両側が小余完備で両脚が全小余極限保存（Lean が強い：原典の特定 K の存在・保存より強い）。結論：同じ引き戻しに全 K-余極限が存在し、その元の全余錐の余極限性は両射影での余極限性と同値（結論は一致）。

余極限余錐は余錐圏の始対象である。余錐圏への移行で引き戻しが保たれることを使えば、始対象の存在と成分ごとの判定を適用でき、射影による余極限保存も得られる。

:::

:::lemma_ "htt_5_4_5_7" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.pullback_hasSmallKappaFilteredColimits, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.pullback_fst_isKappaAccessibleFunctor, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.pullback_snd_isKappaAccessibleFunctor, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isKappaCompact_pullback_of_components") (uses := "htt_1_1_2_4, htt_5_3_1_7, htt_5_3_4_5")
*HTT 補題 5.4.5.7*　引き戻しのフィルター余極限とコンパクト対象（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=455)）。対応表の状態：一部（stronger-hyp）。

*主張*　引き戻しの両側が小さい $`\kappa`-濾過余極限を持ち、底への両関手が保存するなら、引き戻しもそれらを持つ。両成分と底での像が $`\kappa`-コンパクトな対象は、引き戻しでも $`\kappa`-コンパクトである。

KB-W2原文・型再照合：仮定：同じ濃度 μ の filtered 余極限を両脚が保存する strict categorical pullback（Lean が強い：compact 性の部分には正則 κ\<μ と IsCardinalChangeBound κ μ の冪評価を追加）。結論：(1) 元の引き戻しの小 μ-filtered 余極限の存在、(2) 両成分と共通像が μ-compact なら同じ頂点が μ-compact（この条件の下で一致）。射影の保存は同じ余極限存在の宣言から得る。

成分で余極限を計算した上で、写像空間のホモトピー引き戻しと濾過余極限の交換を使う。コンパクト性の仮定には、共通の底での像も含まれる。

:::

:::lemma_ "htt_5_4_5_13" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.isKappaCompact_smallSourceCosliceVertex") (uses := "htt_1_1_2_4, htt_5_3_1_7, htt_5_3_4_5")
*HTT 補題 5.4.5.13*　小コンパクト図式の余錐のコンパクト性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=459)）。対応表の状態：一部（stronger-hyp）。

*主張*　$`\kappa`-濾過余極限を持つ ∞ 圏で、$`\kappa`-コンパクト対象だけからなる $`\kappa`-小な余錐は、その底の図式の下の圏でも $`\kappa`-コンパクトである。

KB-W2原文・型再照合：仮定：非可算正則 κ、κ-small な準圏形状と全頂点が κ-compact な図式・κ-compact な余錐頂点（Lean が強い：周囲 C は全小余完備、形状は準圏）。結論：同じ全余錐自身が Cp/ の κ-compact 対象（この場合に一致）。頂点だけの compact 性に弱めていない。

余錐圏を自然変換の圏と評価の引き戻しとして扱い、点ごとのコンパクト性を使う。原典の表示には $`C^\tau` と $`C^\kappa` が混在する。この記述では、仮定と結論で指定される $`\kappa`-コンパクト性を用いた。

:::

:::lemma_ "htt_5_4_5_14" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sourceCoslice_hasSmallKappaFilteredColimits") (uses := "htt_1_1_2_4")
*HTT 補題 5.4.5.14*　余スライスのフィルター余極限の存在（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=460)）。対応表の状態：一部（special）。

*主張*　$`C` が小さい $`\tau`-濾過余極限を持てば、小さい図式 $`p:K\to C` の下の圏 $`C_{p/}` もそれらを持つ。

KB-W2原文・型再照合：仮定：正則 τ と C の小 τ-filtered 余極限の存在（Lean が強い：固定図式を一点 x に限定）。結論：同じ Cx/ は小 τ-filtered 余極限を持つ（この場合に一致）。任意の小形状の p についての存在まではこの宣言で述べていない。

始域の図式を固定した自然変換の余極限を考える。濾過性により固定した図式を定値図式の余極限として回収できるので、余錐の頂点の余極限から新たな余錐が得られる。

:::

:::proposition "htt_5_4_5_15" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.isInitialVertex_iff_trivialKanFibration, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.qCatEquivalenceOfTrivialKanFibration, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.isKappaAccessible_iff_equivalence, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isKappaCompact_iff_equivalence") (uses := "htt_1_1_2_4, htt_4_1_1_3, htt_4_2_3_6, htt_5_3_1_20, htt_5_3_5_10, htt_5_3_5_11, htt_5_4_5_13, htt_5_4_5_14")
*HTT 命題 5.4.5.15*　余スライスの到達可能性とコンパクト対象の判定（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=460)）。対応表の状態：一部（special）。

*主張*　$`\kappa\ll\tau` とし、$`C` が $`\tau`-可到達で、$`p` がその $`\tau`-コンパクト対象からなる $`\kappa`-小図式なら、$`C_{p/}` は $`\tau`-可到達で、そのコンパクト性は余錐の頂点で判定できる。

KB-W2原文・型再照合：仮定：τ-accessible な C と τ-compact な始対象 x の一点図式（Lean が強い：一般の κ-small compact 図式を始対象の一点に限定）。結論：同じ Cx/ は C への射影が全準圏同値なので τ-accessible、かつ元の余錐の τ-compact 性は射影頂点の τ-compact 性と同値（この場合に両結論が一致）。

余錐の頂点が $`\tau`-コンパクトなら余錐全体も $`\tau`-コンパクトになる。頂点をコンパクトなものに取り替えた余錐で下の圏を生成することから、逆向きの判定も得られる。

:::

:::corollary "htt_5_4_5_16" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.isInitialVertex_iff_trivialKanFibration, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.qCatEquivalenceOfTrivialKanFibration, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.isAccessible_iff_equivalence") (uses := "htt_1_1_2_4, htt_5_4_2_1, htt_5_4_5_15")
*HTT 系 5.4.5.16*　小図式の余スライスの到達可能性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=461)）。対応表の状態：一部（special）。

*主張*　可到達 ∞ 圏 $`C` において、小さい図式 $`p:K\to C` の下の圏 $`C_{p/}` は可到達である。

KB-W2原文・型再照合：仮定：accessible な C と始対象 x の一点図式（Lean が強い）。結論：元の Cx/ の射影は終始対象の境界判定から trivial Kan fibration であり、C と全同値なので accessible（この場合に一致）。一般の小図式の下圏の生成性を結論したとは数えない。

図式の大きさと各頂点のコンパクト性を同時に抑えられる正則基数を選んで、基数を指定した前項の判定を適用する。

:::

# 5.4.6 Accessibility of Fiber Products

%%%
number := false
tag := "htt-5-4-6"
%%%

:::proposition "htt_5_4_6_6" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.pullback_isAccessible, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.pullback_isKappaAccessibleFunctor_iff_components, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.pullback_fst_isKappaAccessibleFunctor, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.pullback_snd_isKappaAccessibleFunctor")
*HTT 命題 5.4.6.6*　到達可能関手の引き戻しの到達可能性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=465)）。対応表の状態：一部（special）。

*主張*　可到達 ∞ 圏の間の可到達関手のホモトピー引き戻しは可到達であり、可到達圏からそこへの関手の可到達性は両射影への合成で判定できる。

KB-W2原文・型再照合：仮定：accessible な三準圏と accessible な両脚（Lean が強い：元の平方を一方が categorical lifting を持つ strict pullback として与える）。結論：同じ引き戻しの accessibility、両射影の accessibility、およびその引き戻しへの関手の accessibility の成分判定（この模型の場合に一致）。共通の正則濃度に各保存性を上げて同じ iff を適用できる。

この判定で二つの射影自身の可到達性も従う。原典の式 $`f:C\to X` は、その直後の二つの合成が定義されるよう引き戻し $`X'` を終域とする。

:::

:::corollary "htt_5_4_6_7" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.isTerminalVertex_iff_trivialKanFibration, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.qCatEquivalenceOfTrivialKanFibration, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.isAccessible_iff_equivalence")
*HTT 系 5.4.6.7*　小図式の上圏の到達可能性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=466)）。対応表の状態：一部（special）。

*主張*　可到達 ∞ 圏 $`C` の小さい図式 $`p:K\to C` の上の圏 $`C_{/p}` は可到達である。

KB-W2原文・型再照合：仮定：accessible な C と終対象 x の一点図式（Lean が強い：p を終対象の一点に限定）。結論：同じ C/x は実際の射影によって C と全準圏同値、従って accessible（この場合に一致）。元の全 Hom と高次単体を保つ同値であり、通常圏の上圏への置換ではない。

錐圏を評価関手のファイバーとして扱う。関手圏が可到達であることと、可到達関手に沿ったホモトピー引き戻しが可到達性を保つことを組み合わせる。

:::

# 5.4.7 Applications

%%%
number := false
tag := "htt-5-4-7"
%%%

:::lemma_ "htt_5_4_7_2" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSet_isPresentable")
*HTT 補題 5.4.7.2*　到達可能準圏の小積と関手の成分判定（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=467)）。対応表の状態：一部（stronger-hyp）。

*主張*　小さい族の可到達 ∞ 圏の積は可到達であり、可到達圏から積への関手の可到達性は各成分で判定できる。

KB-W2原文・型再照合：仮定：小族の各成分が presentable（Lean が強い：原典は accessible のみ）。結論：同じ全単体の積準圏が presentable、従って accessible（この場合の第一結論に一致）。成分余極限の判定もあるが、任意の accessible 関手の成分ごとの iff まではこの二宣言で主張しない。

各圏の余極限とコンパクト生成を一斉に扱える正則基数を選べるのは、因子の族が小さいためである。余極限の保存は積の各座標で検査できる。

:::

:::proposition "htt_5_4_7_7" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rightAdjoint_isAccessible, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.mapJoinCocone_isColimit_of_adjunction")
*HTT 命題 5.4.7.7*　到達可能準圏間の随伴関手の到達可能性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=469)）。対応表の状態：本体にある。

*主張*　可到達 ∞ 圏の間の関手は、左随伴か右随伴のいずれかを持てば可到達である。

仮定：accessible な二準圏と元の左右いずれかの随伴関手（HTT と一致）。結論：右随伴はある正則濃度で filtered 余極限を保存、左随伴は元の全余極限を保存するので始域の accessibility の濃度でも保存（一致）。標的の presentability や宇宙変更の充満忠実性を追加入力にしない。

左随伴としての余極限保存は直接に使える。右随伴の場合には、左随伴が十分大きな基数でコンパクト対象を保つことを利用し、写像空間を通して右随伴の濾過余極限保存を得る。

:::

:::definition "htt_5_4_7_8" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessible, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessibleFunctor")
*HTT 定義 5.4.7.8*　到達可能全部分準圏の定義（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=469)）。対応表の状態：本体にある。

*主張*　可到達 ∞ 圏 $`C` の充満部分圏 $`D` が可到達部分圏であるとは、$`D` 自身と包含 $`D\hookrightarrow C` の双方が可到達であることである。

仮定：accessible な C とその全部分準圏 D（HTT と一致）。結論：D 自身の accessibility と同じ包含関手の accessibility という二条件を、同じ濃度での filtered 余極限保存の意味で表せる（一致）。単なる D の対象集合の小ささではない。

部分圏内に濾過余極限が存在することと、その計算がある基数から周囲の圏と一致することは、別々の条件である。

:::

:::proposition "htt_5_4_7_9" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.limitConeProjection_trivialKanFibration, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.colimitCoconeProjection_trivialKanFibration")
*HTT 例 5.4.7.9*　極限図式と余極限図式の全部分準圏（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=470)）。対応表の状態：一部（component）。

*主張*　可到達 ∞ 圏で小さい $`K`-型の極限または余極限がすべて存在するとき、その極限錐または余極限余錐の圏は対応する図式圏の可到達部分圏となる。

KB-W2原文・型再照合：仮定：C が各 K-極限または K-余極限を持つ準圏（HTT と一致。Lean は C の accessibility を不要とする）。結論：元の極限・余極限図式の全部分準圏から Fun(K,C) への実際の制限が trivial Kan fibration、従って準圏同値（原典中の同値の結論に一致）。包含の accessibility、ひいては accessible subcategory という結論全体は含まない。

普遍的な錐を選ぶ圏から底の図式への制限は同値である。錐をすべての錐の圏に入れる関手には随伴があり、そこから包含の可到達性が従う。余錐にも双対に適用する。

:::

:::proposition "htt_5_4_7_16" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.InitialSectionLifting.cocartesianSectionsEvaluate_isQCatEquivalence")
*HTT 注意 5.4.7.16*　区間上の余カルテジアン切断の始点評価（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=472)）。対応表の状態：本体にある。

*主張*　関手 $`F:C\to D` を分類する $`\Delta^1` 上の余デカルト・ファイブレーションでは、余デカルト切断の圏は始点での評価によって $`C` と同値となる。

仮定：coCartesian fibration M→Δ¹ と始点 0（HTT と一致）。結論：元の coCartesian 切断の全部分準圏から元の始点ファイバーへの実際の評価が準圏同値（一致）。全切断との区別を保持する。

切断の辺が余デカルトであるという条件は、始点の対象からの余デカルト移送を選んでいることを意味する。その選択の空間は可縮であり、始点の評価は自明ファイブレーションになる。

:::

