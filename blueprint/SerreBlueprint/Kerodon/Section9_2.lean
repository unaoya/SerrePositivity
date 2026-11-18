import Verso
import VersoManual
import VersoBlueprint
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.AlgebraicTopology.SimplicialSet.Finite
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Presentable.Finite
import Mathlib.CategoryTheory.Yoneda
import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.Definition
import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.WeakHomotopy
import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.WeakWhitehead
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.FilteredPosetNerve
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.CofinalColimitExistence
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.Definition
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.FiniteColimitClosureUnconditional
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.FiniteCoproductColimitGeneration
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.FiniteCoproductSiftedPreservation
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.FiniteKanReplacementCompact
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.FiniteSpaceGenerators
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.KappaSmallPresentable
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.NativeFilteredPreservation
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.NativePreservationPosetReductionUniverse
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.SmallPosetColimitCompactUniverse
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.SmallQuasicategoryColimitCompact
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.SmallSpaceCompact
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.SpaceCompactCardinals
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.Subcategory
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.CofinalUniverseLift
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.LaxPullbackColimitConeExistence
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.LaxPullbackColimitCriterion
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.PrecompositionEquivalence

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "9.2 Finitary Functors and Compact Objects" =>
%%%
number := false
tag := "kerodon-9-2"
%%%

Kerodon の 9.2 節（[Tag 0639](https://kerodon.net/tag/0639)）の項目と、SerrePositivity・Mathlib の宣言との対応。本文は対応表（research/kerodon-coverage）の判定の理由の要約で、Kerodon の本文の写しではない。

:::proposition "kerodon_9_2_0_1" (lean := "ModuleCat.adj, CategoryTheory.Adjunction.compCoyonedaIso, CategoryTheory.Coyoneda.punitIso, ModuleCat.FilteredColimits.forget_preservesFilteredColimits, Module.finitePresentation_of_projective")
Kerodon Proposition 9.2.0.1（[Tag 063A](https://kerodon.net/tag/063A)）。対応表の状態：一部。

*主張*　結合的環 $`R` 上の左加群 $`M` は、$`\operatorname{Hom}_R(M,-)` が小さいフィルター付き余極限を保つとき、かつそのときに限り有限表示である。

B6型照合：有限自由加群の有限表示があり、階数1では free 随伴と PUnit の coyoneda で Hom 関手を forget と比較し、filtered 余極限保存を得る。任意の左 R-加群で代数的有限表示と Hom の保存性を結ぶ iff は見つからない。

:::

:::definition "kerodon_9_2_0_2" (lean := "CategoryTheory.IsFinitelyPresentable, CategoryTheory.isFinitelyPresentable_iff_preservesFilteredColimits")
Kerodon Definition 9.2.0.2（[Tag 063B](https://kerodon.net/tag/063B)）。対応表の状態：Mathlib にある。

*主張*　小さいフィルター付き余極限を持つ通常の圏で、対象 $`x` は $`\operatorname{Hom}(x,-)` がそれらの余極限を保つときコンパクトである。

仮定：通常圏 C と X。原文は小 filtered 余極限を持つ C、Lean の同値にはその仮定が不要（Lean が弱い）。結論：IsFinitelyPresentable X と coyoneda の X 成分による小 filtered 余極限保存の iff（原文の compact 性に一致）。

:::

:::definition "kerodon_9_2_0_5" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.isCardinalPresentable_of_isKappaSmall") (uses := "kerodon_1_1_0_6, kerodon_3_6_1_1, kerodon_3_6_1_7")
Kerodon Variant 9.2.0.5（[Tag 063E](https://kerodon.net/tag/063E)）。対応表の状態：一部。

*主張*　通常の単体集合の圏において、コンパクト対象であることは有限単体集合であることと同値である。

B6型照合：有限 ⇒ finitely presentable の向きのみ（Mathlib）。自前は κ-small ⇒ κ-presentable。逆向きはない。

:::

# 9.2.1 Filtered Cocompleteness

%%%
number := false
tag := "kerodon-9-2-1"
%%%

Kerodon [Tag 06DA](https://kerodon.net/tag/06DA)

:::proposition "kerodon_9_2_1_1"
Kerodon Proposition 9.2.1.1（[Tag 06DB](https://kerodon.net/tag/06DB)）。対応表の状態：なし。

余積と幾何実現からの全小余極限生成は、有限余極限とfiltered余極限からの同じ生成命題ではない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.hasSmallColimits_of_coproducts_geometricRealizations`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.preservesSmallCoproducts_of_finite_filtered`

:::

:::definition "kerodon_9_2_1_3" (uses := "kerodon_1_4_0_1")
Kerodon Definition 9.2.1.3（[Tag 06DD](https://kerodon.net/tag/06DD)）。対応表の状態：なし。

宇宙で小さい全κ-filtered形状を量化する述語は、原文の指定λ-smallだけに限った二濃度の定義と同じではない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.HasSmallKappaFilteredColimits`

:::

:::proposition "kerodon_9_2_1_7"
Kerodon Proposition 9.2.1.7（[Tag 062W](https://kerodon.net/tag/062W)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：宇宙小の κ-filtered 余極限の存在述語と、余積・幾何学的実現から全小余極限を作る型はある。κ-small な余極限と λ-small κ-filtered な余極限から λ-余完備性を得る濃度分解は見つからない。

:::

:::corollary "kerodon_9_2_1_9" (lean := "SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits.hasSmallKappaFilteredColimits")
Kerodon Corollary 9.2.1.9（[Tag 03DK](https://kerodon.net/tag/03DK)）。対応表の状態：一部。

*主張*　小さい正則基数 $`\kappa` に対し、無限圏が余完備であることは、$`\kappa`-余完備であり、小さい $`\kappa`-フィルター付き余極限を持つことと同値である。

B6型照合：全小余極限があれば小さい κ-filtered 余極限もある型は確認できる。任意の小さい κ について κ-small な余極限と小 κ-filtered 余極限を合わせて全小余極限を得る逆向きは見つからない。

:::

:::corollary "kerodon_9_2_1_10"
Kerodon Corollary 9.2.1.10（[Tag 06DJ](https://kerodon.net/tag/06DJ)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：全小余極限から小 filtered 余極限への制限と、余積・実現による全小余極限の構成はある。有限余極限と λ-small filtered 余極限を仮定して λ-small な任意の形状に余極限を作る型は見つからない。

:::

:::proposition "kerodon_9_2_1_11"
Kerodon Proposition 9.2.1.11（[Tag 062K](https://kerodon.net/tag/062K)）。対応表の状態：なし。

cofinal posetの存在に原文の必要なλ-small性の型がなく、同じλにおける余極限存在のiffは導けない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.exists_cofinal_kappaFiltered_poset`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.hasColimit_of_rightCofinalRestriction`

:::

:::corollary "kerodon_9_2_1_12" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.HasSmallKappaFilteredColimits, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.exists_cofinal_kappaFiltered_poset, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.hasColimit_of_rightCofinalRestriction, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.isRightCofinal_ulift, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isKappaFiltered_nerve_of_cardinalFiltered")
Kerodon Corollary 9.2.1.12（[Tag 062M](https://kerodon.net/tag/062M)）。対応表の状態：本体にある。

*主張*　小さい正則基数 $`\kappa` に対し、無限圏が小さい $`\kappa`-フィルター付き余極限を持つことは、各小さい $`\kappa`-有向半順序集合 $`A` に対して $`N(A)` 添字の余極限を持つことと同値である。

小さい同じκ-filtered形状にexists\_cofinal\_kappaFiltered\_posetを適用し、全poset余極限の仮定をその制限へ入れてhasColimit\_of\_rightCofinalRestrictionで戻す。逆はnerveのκ-filtered性による特殊化で直接得る。専用の合成iff名は不要。

:::

:::corollary "kerodon_9_2_1_13"
Kerodon Corollary 9.2.1.13（[Tag 039G](https://kerodon.net/tag/039G)）。対応表の状態：なし。

κ=ℵ0のcofinal posetが得られても指定λ-small性が型にない。原文の同じ濃度境界のiffとしない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.exists_cofinal_kappaFiltered_poset`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.hasColimit_of_rightCofinalRestriction`

:::

:::proposition "kerodon_9_2_1_14"
Kerodon Proposition 9.2.1.14（[Tag 062R](https://kerodon.net/tag/062R)）。対応表の状態：なし。

N(Idem)のfiltered性とその余極限による冪等完備性は、指定κ-smallな形状の小性と全形状の余極限存在を結ぶ型を含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.isIdempotentComplete_iff_hasColimits`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.idemShape_isKappaFiltered`

:::

:::proposition "kerodon_9_2_1_15"
Kerodon Proposition 9.2.1.15（[Tag 06DK](https://kerodon.net/tag/06DK)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：準圏と通常圏に宇宙小の濃度別余極限の述語はある。三つの正則濃度で (κ,μ) の存在を (κ,λ) と (λ,μ) の存在に分解する型は見つからない。

:::

:::corollary "kerodon_9_2_1_16"
Kerodon Corollary 9.2.1.16（[Tag 06DL](https://kerodon.net/tag/06DL)）。対応表の状態：なし。

通常圏のHasCardinalFilteredColimits.of\_leは原文の∞圏の余極限への比較を含まない。

宣言：`CategoryTheory.HasCardinalFilteredColimits.of_le`

:::

:::corollary "kerodon_9_2_1_17"
Kerodon Corollary 9.2.1.17（[Tag 06DM](https://kerodon.net/tag/06DM)）。対応表の状態：なし。

通常圏の余極限存在の単調性は原文の∞圏におけるλ-small/λ-filteredの分解と比較されていない。

宣言：`CategoryTheory.HasCardinalFilteredColimits.of_le`

:::

# 9.2.2 Finitary Functors

%%%
number := false
tag := "kerodon-9-2-2"
%%%

Kerodon [Tag 062B](https://kerodon.net/tag/062B)

:::definition "kerodon_9_2_2_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.PreservesKappaFilteredColimits, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.PreservesSmallKappaFilteredColimits")
Kerodon Definition 9.2.2.1（[Tag 039F](https://kerodon.net/tag/039F)）。対応表の状態：一部。

*主張*　小さいフィルター付き余極限を持つ無限圏からの関手が finitary であるとは、小さいフィルター付き無限圏を添字とする余極限を全て保つことである。そのような関手が張る充満部分圏を $`\operatorname{Fun}^{\mathrm{fin}}` と書く。

PreservesSmallKappaFilteredColimitsのκ=ℵ0は原文の同じFのfinitary条件を直接与える。全関手準圏のその条件による全部分圏という追加の構成成分はこの引用だけに含まない。

:::

:::definition "kerodon_9_2_2_3" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.PreservesKappaFilteredColimits, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.PreservesSmallKappaFilteredColimits")
Kerodon Definition 9.2.2.3（[Tag 05Y6](https://kerodon.net/tag/05Y6)）。対応表の状態：一部。

*主張*　小さい正則基数 $`\kappa` について、小さい $`\kappa`-フィルター付き余極限を持つ無限圏からの関手が $`\kappa`-finitary であるとは、それらの余極限をすべて保つことである。そのような関手が張る充満部分圏を $`\operatorname{Fun}^{\kappa\text{-}\mathrm{fin}}` と書く。

PreservesSmallKappaFilteredColimitsの同じκは原文の同じFのfinitary条件を直接与える。全関手準圏のその条件による全部分圏という追加の構成成分はこの引用だけに含まない。

:::

:::definition "kerodon_9_2_2_6" (uses := "kerodon_1_4_0_1")
Kerodon Definition 9.2.2.6（[Tag 062F](https://kerodon.net/tag/062F)）。対応表の状態：なし。

宇宙小形状すべてでの保存述語は原文の指定λ-smallだけの保存と同じ条件ではない。二つの大きさを比較する型がない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.PreservesSmallKappaFilteredColimits`

:::

:::definition "kerodon_9_2_2_14"
Kerodon Notation 9.2.2.14（[Tag 06DT](https://kerodon.net/tag/06DT)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：PrL の対象は presentable、射は全小余極限を保つ。κ-filtered かつ λ-small な形状で対象と射を制限し、さらに μ-small な対象へ絞る QC 部分圏は見つからない。

:::

:::proposition "kerodon_9_2_2_21"
Kerodon Proposition 9.2.2.21（[Tag 06DV](https://kerodon.net/tag/06DV)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：全小余極限保存を小余積と有限余極限の保存から導く型はある。κ-small な全形状と λ-small κ-filtered 形状の保存を組み合わせる二濃度の判定は見つからない。

:::

:::corollary "kerodon_9_2_2_22"
Kerodon Corollary 9.2.2.22（[Tag 06DW](https://kerodon.net/tag/06DW)）。対応表の状態：なし。

引用は余極限の存在とaccessible性の入力で、同じFのκ-small余極限保存と全保存を結ぶ型ではない。

宣言：`SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits.isKappaAccessibleFunctor`

:::

:::corollary "kerodon_9_2_2_23" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.preservesSmallCoproducts_of_finite_filtered, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.preservesSmallColimits_of_coproducts_finite")
Kerodon Corollary 9.2.2.23（[Tag 06DX](https://kerodon.net/tag/06DX)）。対応表の状態：一部。

*主張*　正則基数 $`\lambda` と $`\lambda`-余完備な無限圏 $`C` に対し、$`C` からの関手が $`\lambda`-余連続であることは、有限余極限と $`\lambda`-小フィルター付き余極限を保つことと同値である。

Cを全小余完備、Fを全小filtered余極限保存にも強めると二つのpreservesSmall補題により同じFの全小余極限保存を直接得る。指定λ-smallだけを仮定する場合は含まない。

:::

:::corollary "kerodon_9_2_2_24" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.preservesSmallCoproducts_of_finite_filtered, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.preservesSmallColimits_of_coproducts_finite")
Kerodon Corollary 9.2.2.24（[Tag 06DY](https://kerodon.net/tag/06DY)）。対応表の状態：一部。

*主張*　余完備な無限圏からの関手が余連続であることは、有限余極限と小さいフィルター付き余極限の両方を保つことと同値である。

有限余極限保存から有限余積保存を取り、preservesSmallCoproducts\_of\_finite\_filteredで小余積保存、preservesSmallColimits\_of\_coproducts\_finiteで同じFの全小余極限保存を得る。右⇒左の向きに一致する。

:::

:::proposition "kerodon_9_2_2_25"
Kerodon Proposition 9.2.2.25（[Tag 06DZ](https://kerodon.net/tag/06DZ)）。対応表の状態：なし。

全宇宙小posetでの判定は原文の指定λ-small posetに対する判定と異なる量化。必要な添字のλ-small性が引用にない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.Compact.preservesKappaFilteredColimits_of_poset`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.exists_cofinal_kappaFiltered_poset`

:::

:::corollary "kerodon_9_2_2_26" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.Compact.preservesKappaFilteredColimits_of_poset")
Kerodon Corollary 9.2.2.26（[Tag 06E0](https://kerodon.net/tag/06E0)）。対応表の状態：本体にある。

*主張*　小さい正則基数 $`\kappa` について、小さい $`\kappa`-フィルター付き余極限を持つ無限圏からの関手が $`\kappa`-finitary であることは、小さい $`\kappa`-有向半順序集合 $`A` の神経で添字付けた余極限をすべて保つことと同値である。

仮定：小さい正則 κ、二つの quasicategory、κ-directed poset の nerve 上での保存。Lean は C 全体の余完備性を要求しない（Lean が弱い）。結論：poset 版の保存から PreservesKappaFilteredColimits κ F。逆は保存の定義を κ-filtered nerve に適用する向き（原文の iff と一致）。

:::

:::corollary "kerodon_9_2_2_27"
Kerodon Corollary 9.2.2.27（[Tag 06E1](https://kerodon.net/tag/06E1)）。対応表の状態：なし。

全宇宙小posetでの保存判定は指定λ-smallだけの量化に比較されていない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.Compact.preservesKappaFilteredColimits_of_poset`

:::

:::corollary "kerodon_9_2_2_28" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.Compact.preservesKappaFilteredColimits_of_poset")
Kerodon Corollary 9.2.2.28（[Tag 06E2](https://kerodon.net/tag/06E2)）。対応表の状態：本体にある。

*主張*　小さいフィルター付き余極限を持つ無限圏からの関手が finitary であることは、すべての小さい有向半順序集合 $`A` に対して $`N(A)` 添字の余極限を保つことと同値である。

仮定：Quasicategory C,D と小さい directed poset 上の保存。preservesKappaFilteredColimits\_of\_poset の κ=ℵ₀ を取る（Kerodon と一致）。結論：一般の小 filtered 形状で保存し、逆はその定義の poset への制限（原文と一致）。

:::

:::proposition "kerodon_9_2_2_29"
Kerodon Proposition 9.2.2.29（[Tag 062T](https://kerodon.net/tag/062T)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：宇宙小の κ-filtered 余極限保存と、より大きい濃度で filtered な形状への制限はある。(κ,μ)-finitary 性を (κ,λ) と (λ,μ) の二条件に分ける iff は見つからない。

:::

:::corollary "kerodon_9_2_2_30"
Kerodon Corollary 9.2.2.30（[Tag 062U](https://kerodon.net/tag/062U)）。対応表の状態：なし。

引用of\_leはcompact性の基数単調性で、原文の同じFの二種類の保存性を分解する型ではない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.PreservesKappaFilteredColimits.of_le`

:::

:::corollary "kerodon_9_2_2_31"
Kerodon Corollary 9.2.2.31（[Tag 062V](https://kerodon.net/tag/062V)）。対応表の状態：なし。

compact性の基数単調性は同じ関手Fのfinitary判定の型ではない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.PreservesKappaFilteredColimits.of_le`

:::

# 9.2.3 Example: Sequential Cocompleteness

%%%
number := false
tag := "kerodon-9-2-3"
%%%

Kerodon [Tag 06E3](https://kerodon.net/tag/06E3)

:::definition "kerodon_9_2_3_1" (uses := "kerodon_1_4_0_1, kerodon_4_9_1_22")
Kerodon Definition 9.2.3.1（[Tag 06E4](https://kerodon.net/tag/06E4)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：κ の始順序の nerve の filtered 性、個別図式の保存余極限、および自然数列についての保存定理はある。任意の正則 κ の Ord\_\{\<κ\} を固定した存在と保存の一対の定義は見つからない。

:::

:::definition "kerodon_9_2_3_4"
Kerodon Notation 9.2.3.4（[Tag 06E7](https://kerodon.net/tag/06E7)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：全小余極限を保つ presentable 圏の準圏と、自然数列の余極限保存の定理はある。κ-順次余完備な対象と κ-順次余極限保存射だけを持つ QC の部分圏および λ-small 版は見つからない。

:::

:::proposition "kerodon_9_2_3_5"
Kerodon Proposition 9.2.3.5（[Tag 06E8](https://kerodon.net/tag/06E8)）。対応表の状態：なし。

線形順序の共終性と指定cofinal写像に沿う余極限比較は候補だが、原文の同じQへOrd\_\<cf(Q)からのcofinal写像を供給する型を確認していない。自然数部分列の比較だけをこのiffの特殊化と数えない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isColimitCone_iff_restrict_rightCofinal`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialSubsequenceColimitVertexIso`

:::

:::proposition "kerodon_9_2_3_6"
Kerodon Proposition 9.2.3.6（[Tag 06E9](https://kerodon.net/tag/06E9)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：κ の順序の nerve が κ-filtered であることと、一般の κ-filtered 準圏へのある poset からの余終写像はある。κ⁺-small な任意の形状を指定の順序 κ で検査できる型は見つからない。

:::

:::corollary "kerodon_9_2_3_8"
Kerodon Corollary 9.2.3.8（[Tag 06EB](https://kerodon.net/tag/06EB)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：可算個の単体を持つ X の有限段階の通常余極限と、自然数列の余終部分列の比較はある。可算 filtered 準圏の全図式に対して自然数列へ制限し、存在と保存を往復する型は見つからない。

:::

:::corollary "kerodon_9_2_3_9" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.hasPreservedColimit_countable_op_of_finite_sequential")
Kerodon Corollary 9.2.3.9（[Tag 06EC](https://kerodon.net/tag/06EC)）。対応表の状態：一部。

*主張*　正則基数 $`\kappa` に対し、無限圏が $`\kappa^+`-余完備であることは、$`\kappa`-余完備で $`\kappa` に沿う列の余極限を持つことと同値である。その場合、そこからの関手が $`\kappa^+`-余連続であることは、$`\kappa`-余連続で $`\kappa` に沿う列の余極限を保つことと同値である。

B6型照合：一般の κ の順序形状の filtered 性と、有限余極限・自然数列を使った可算形状の保存余極限の構成はある。任意の正則 κ と κ⁺ に対する存在・保存の判定は見つからない。

:::

:::corollary "kerodon_9_2_3_10" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.hasPreservedColimit_countable_op_of_finite_sequential")
Kerodon Corollary 9.2.3.10（[Tag 06ED](https://kerodon.net/tag/06ED)）。対応表の状態：一部。

*主張*　無限圏が可算余極限を持つことは、有限余極限と自然数列の余極限を持つことと同値である。その場合、そこからの関手が可算余極限を保つことは、有限余極限と自然数列の余極限を保つことと同値である。

B6型照合：一つの宇宙の小さい可算 B に対し、有限形状と自然数列の余極限の存在・保存を仮定して Bᵒᵖ 上の保存余極限を作る。濃度による aleph1 の一般の存在・保存 iff としては確認できない。

:::

:::corollary "kerodon_9_2_3_11"
Kerodon Corollary 9.2.3.11（[Tag 06EE](https://kerodon.net/tag/06EE)）。対応表の状態：なし。

通常圏の余極限存在とcompact性の単調性は、原文の∞圏と関手のsequential余極限による判定と異なる主張。

宣言：`CategoryTheory.HasCardinalFilteredColimits.of_le`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.PreservesKappaFilteredColimits.of_le`

:::

:::corollary "kerodon_9_2_3_12"
Kerodon Corollary 9.2.3.12（[Tag 06EF](https://kerodon.net/tag/06EF)）。対応表の状態：なし。

通常圏の余極限存在とcompact性の単調性を∞圏の同じ逐次余極限判定へ移す比較がない。

宣言：`CategoryTheory.HasCardinalFilteredColimits.of_le`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.PreservesKappaFilteredColimits.of_le`

:::

# 9.2.4 Fiber Products of Filtered ∞-Categories

%%%
number := false
tag := "kerodon-9-2-4"
%%%

Kerodon [Tag 06EG](https://kerodon.net/tag/06EG)

:::proposition "kerodon_9_2_4_1"
Kerodon Proposition 9.2.4.1（[Tag 06EH](https://kerodon.net/tag/06EH)）。対応表の状態：なし。

積射影に沿うstrict pullbackのfiltered性は原文の一般categorical pullbackと同じものではなく、right cofinalな二射影との比較もない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.piSSetSmall_isKappaFiltered`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.piSSetSmallProjection_pullback_isKappaFiltered`

:::

:::theorem "kerodon_9_2_4_3" (uses := "kerodon_1_4_0_1, kerodon_4_6_4_22, kerodon_7_1_7_5, kerodon_9_1_1_16, kerodon_9_1_4_5, kerodon_9_1_4_16, kerodon_9_1_4_18, kerodon_9_2_3_1, kerodon_9_2_4_5")
Kerodon Theorem 9.2.4.3（[Tag 06EL](https://kerodon.net/tag/06EL)）。対応表の状態：なし。

pullbackのκ-filtered余極限の存在と保存は、そのpullback自体のλ-filtered性や射影のright cofinal性ではない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.pullback_hasSmallKappaFilteredColimits`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.pullback_fst_isKappaAccessibleFunctor`

:::

:::lemma_ "kerodon_9_2_4_5" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_3_6_13, kerodon_7_1_1_13, kerodon_7_2_1_3, kerodon_7_2_2_11, kerodon_7_2_3_1, kerodon_7_2_3_4, kerodon_9_1_4_18")
Kerodon Lemma 9.2.4.5（[Tag 06EP](https://kerodon.net/tag/06EP)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：右余終射の左ファイブレーションに沿う厳密引き戻しは右余終。両脚が右余終で逐次余極限を保つという条件からホモトピー引き戻しに頂点を得る型は見つからない。

:::

# 9.2.5 Compact Objects

%%%
number := false
tag := "kerodon-9-2-5"
%%%

Kerodon [Tag 0649](https://kerodon.net/tag/0649)

*06-catinfty-ind-presentable.html — 4. κ-compact 対象*

\`\`\`text
def IsKappaCompact (κ : Cardinal.\{u\}) \{C : SSet.\{max u v\}\} \[Quasicategory C\]
    (x : C \_⦋0⦌) : Prop :=
  PreservesKappaFilteredColimits.\{u, v\} κ (C := C) (covariantRepresentableInfinity x)
\`\`\`

$`\mathrm{Map}(x,-)` が小さい κ-filtered 余極限を保つこと。

- 表現可能前層は $`\mathcal P(C)` の中でも Ind の中でも κ-compact（\`indYoneda\_isKappaCompact\`、F2/Compact/IndCompact）

- retract で閉じる。有限余極限で閉じることは、交換定理を仮定にとった形で証明されている（a7 待ち）

- *compact 生成*：$`C` が冪等完備なら $`C\simeq\mathrm{Ind}_\kappa(C)^\kappa`（\`compactGenerationEquivalence\`、F2/Ind/CompactGeneration）

:::definition "kerodon_9_2_5_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsCompact, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.isKappaCompact_aleph0_iff_filtered")
Kerodon Definition 9.2.5.1（[Tag 064A](https://kerodon.net/tag/064A)）。対応表の状態：本体にある。

*主張*　小さいフィルター付き余極限を持つ無限圏で、対象 $`x` は余表現関手 $`\operatorname{Hom}_C(x,-)` がそれらの余極限を保つときコンパクトである。

仮定：Quasicategory C と頂点 x。Lean は C の全 filtered 余極限の存在を定義に要求しない（Lean が弱い）。結論：IsCompact は ℵ₀-compact、引用 iff は covariantRepresentableInfinity x の filtered 余極限保存（原文と一致）。

:::

:::definition "kerodon_9_2_5_6" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.kappaCompactObjects")
Kerodon Definition 9.2.5.6（[Tag 064F](https://kerodon.net/tag/064F)）。対応表の状態：本体にある。

*主張*　小さい正則基数 $`\kappa` について、小さい $`\kappa`-フィルター付き余極限を持つ無限圏で、$`x` は $`\operatorname{Hom}_C(x,-)` がそれらの余極限を保つとき $`\kappa`-コンパクトである。その充満部分圏を $`C_{<\kappa}` と書く。

仮定：Quasicategory C、κ、頂点 x。定義は正則性と全 κ-filtered 余極限存在を要求しない（Lean が弱い）。結論：IsKappaCompact は共表現可能関手の小 κ-filtered 余極限保存で、kappaCompactObjects は該当頂点の充満部分複体（原文と一致）。

:::

:::definition "kerodon_9_2_5_10" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.isCardinalPresentable_of_isKappaSmall") (uses := "kerodon_1_1_0_6, kerodon_1_1_3_9, kerodon_1_1_3_11, kerodon_4_9_4_1, kerodon_4_9_4_10, kerodon_8_4_2_1, kerodon_9_2_0_5, kerodon_9_2_5_24")
Kerodon Variant 9.2.5.10（[Tag 064K](https://kerodon.net/tag/064K)）。対応表の状態：一部。

*主張*　小さい正則基数 $`\kappa` と小さい単体集合 $`X` に対し、通常の単体集合の圏で $`X` が $`\kappa`-コンパクトであることは $`X` が $`\kappa`-小さいことと同値である。

B6型照合：κ-small ⇒ κ-presentable の向きのみ（ℵ₀ は Mathlib）。逆向きはない。

:::

:::definition "kerodon_9_2_5_11"
Kerodon Variant 9.2.5.11（[Tag 064L](https://kerodon.net/tag/064L)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常のコンパクト束要素について有限個の原子による判定はある。任意の正則 κ に対し、部分集合の濃度と Sub(Y) の nerve 内の共表現可能関手の κ-filtered 余極限保存を比較する iff は見つからない。

:::

:::definition "kerodon_9_2_5_12"
Kerodon Definition 9.2.5.12（[Tag 064M](https://kerodon.net/tag/064M)）。対応表の状態：なし。

IsKappaCompactの宇宙小形状の全保存は、原文の指定λ-smallかつκ-filtered形状と数値μのHom対象を同時に扱う定義ではない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.PreservesKappaFilteredColimits`

:::

:::proposition "kerodon_9_2_5_21"
Kerodon Proposition 9.2.5.21（[Tag 064T](https://kerodon.net/tag/064T)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：宇宙小の κ-compact 性の定義とより大きい濃度への単調性はある。三濃度の (κ,μ)-compact 性を (κ,λ) と (λ,μ) の両条件に分ける iff は見つからない。

:::

:::corollary "kerodon_9_2_5_22" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.of_le")
Kerodon Corollary 9.2.5.22（[Tag 064U](https://kerodon.net/tag/064U)）。対応表の状態：一部。

*主張*　小さい正則基数 $`\kappa\trianglelefteq\lambda` と小さい $`\kappa`-フィルター付き余極限を持つ無限圏 $`C` で、対象が $`\kappa`-コンパクトであることは、$`(\kappa,\lambda)`-コンパクトかつ $`\lambda`-コンパクトであることと同値である。

PreservesKappaFilteredColimits.of\_leを同じcovariantRepresentableInfinityに適用すると原文のκ-compact⇒λ-compactという右辺一成分を直接得る。(κ,λ)-compactとの全同値は含まない。

:::

:::corollary "kerodon_9_2_5_23" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.of_le, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.isKappaCompact_aleph0_iff_filtered")
Kerodon Corollary 9.2.5.23（[Tag 064V](https://kerodon.net/tag/064V)）。対応表の状態：一部。

*主張*　小さい正則基数 $`\lambda` と小さいフィルター付き余極限を持つ無限圏 $`C` で、対象がコンパクトであることは、$`(\aleph_0,\lambda)`-コンパクトかつ $`\lambda`-コンパクトであることと同値である。

κ=ℵ0のcompact判定と保存の基数単調性から同じ対象のcompact⇒λ-compactを直接得る。二濃度の残りの条件は含まない。

:::

:::proposition "kerodon_9_2_5_24" (uses := "kerodon_1_4_0_1, kerodon_7_4_1_22")
Kerodon Proposition 9.2.5.24（[Tag 064W](https://kerodon.net/tag/064W)）。対応表の状態：なし。

宇宙小の全κ-filtered余極限についてのκ-compact性の閉性は、λ-smallのみをテストする(κ,λ)-compact性とは異なる仮定・結論。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.isKappaCompact_smallQuasicategoryColimit_universe`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.isKappaCompact_smallPosetColimit_universe`

:::

:::corollary "kerodon_9_2_5_25" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.isKappaCompact_smallQuasicategoryColimit_universe, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.isKappaCompact_smallPosetColimit_universe, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.isKappaCompact_finiteColimit") (uses := "kerodon_1_4_0_1")
Kerodon Corollary 9.2.5.25（[Tag 064X](https://kerodon.net/tag/064X)）。対応表の状態：一部。

*主張*　小さい正則基数 $`\kappa` と小さい $`\kappa`-フィルター付き余極限を持つ無限圏において、$`\kappa`-コンパクト対象は $`\kappa`-小余極限で閉じる。

B6型照合：原文は任意の小さい正則 κ について κ-small 余極限で閉じる主張。引用は非可算の小 quasicategory・poset 形状と有限形状の結果。

:::

:::corollary "kerodon_9_2_5_26" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.isKappaCompact_finiteColimit, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.hasFiniteColimits_kappaCompactObjects")
Kerodon Corollary 9.2.5.26（[Tag 064Y](https://kerodon.net/tag/064Y)）。対応表の状態：本体にある。

*主張*　小さいフィルター付き余極限を持つ無限圏において、コンパクト対象は有限余極限で閉じる。

仮定：有限単体集合 K の図式の余錐 a が余極限で、全値が κ-compact、κ≥ℵ₀。κ=ℵ₀ では原文の状況を含む（Lean が弱い）。結論：a の頂点は κ-compact（有限余極限閉性と一致）。

:::

# 9.2.6 Finiteness Conditions on Kan Complexes

%%%
number := false
tag := "kerodon-9-2-6"
%%%

Kerodon [Tag 067N](https://kerodon.net/tag/067N)

:::definition "kerodon_9_2_6_1" (lean := "SSet.Finite, SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence")
Kerodon Definition 9.2.6.1（[Tag 067P](https://kerodon.net/tag/067P)）。対応表の状態：本体にある。

*主張*　Kan 複体 $`X` が本質的に有限であるとは、有限単体集合 $`K` からの弱ホモトピー同値 $`K\to X` が存在することをいう。

同じKan複体Xについて∃K:SSet, K.Finiteかつ∃f:K⟶X, IsWeakHomotopyEquivalence fという既存の型の存在量化が原文の定義全体に一致する。専用名の欠如を不足としない。

:::

:::proposition "kerodon_9_2_6_3"
Kerodon Proposition 9.2.6.3（[Tag 067R](https://kerodon.net/tag/067R)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：有限単体集合の Kan 置換の族と単体集合の有限形状を押し出しで組む帰納法はある。空間圏内で一点の有限余極限閉包に入ることと本質的有限性の iff は見つからない。

:::

:::corollary "kerodon_9_2_6_4"
Kerodon Corollary 9.2.6.4（[Tag 067T](https://kerodon.net/tag/067T)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：有限 CW 複体の細胞数による判定と有限単体集合の Kan 置換はある。Sing(Y) とのホモトピー同値があることを任意の Kan 複体の本質的有限性と往復する型は見つからない。

:::

:::corollary "kerodon_9_2_6_5" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.finiteKanReplacement_isCompact, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.finiteSpaceGeneratorVertex_isCompact")
Kerodon Corollary 9.2.6.5（[Tag 067U](https://kerodon.net/tag/067U)）。対応表の状態：一部。

*主張*　本質的に有限な Kan 複体は、空間の無限圏の対象としてコンパクトである。

Xを有限単体集合の標準Kan置換に限ると、有限生成対象のcompact性は同じXのSpace内compact性を直接返す。任意のessentially finite Xへの輸送と逆向きは含まない。

:::

:::definition "kerodon_9_2_6_6"
Kerodon Definition 9.2.6.6（[Tag 067W](https://kerodon.net/tag/067W)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：指定の生成族の像の頂点 retract と空間の有限単体集合由来の生成族はある。任意の本質的有限な Kan 複体から h Kan 内で retract となることを一つにした述語は見つからない。

:::

:::proposition "kerodon_9_2_6_7"
Kerodon Proposition 9.2.6.7（[Tag 067X](https://kerodon.net/tag/067X)）。対応表の状態：なし。

compact generatingのretract判定は、原文の有限単体集合によるdominationと全空間のhS内retractを結ぶ同じ比較を型に含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompactGenerating.compact_iff_retract`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.spaceCompactGeneratorInclusion_isCompactGenerating`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.finiteSpaceGeneratorVertex_isCompact`

:::

:::proposition "kerodon_9_2_6_9" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.smallKanObject_isKappaCompact, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.exists_spaceCompactCardinal")
Kerodon Proposition 9.2.6.9（[Tag 0680](https://kerodon.net/tag/0680)）。対応表の状態：一部。

*主張*　非可算正則基数 $`\kappa` に対し、Kan 複体が本質的に $`\kappa`-小さいこと、一点を含み $`\kappa`-小余極限で閉じる空間の最小の充満部分圏に属すること、空間として $`\kappa`-コンパクトであることは同値である。

B6型照合：非可算正則 μ について μ-small Kan 複体が μ-compact の向きのみ。

:::

:::proposition "kerodon_9_2_6_10"
Kerodon Proposition 9.2.6.10（[Tag 0681](https://kerodon.net/tag/0681)）。対応表の状態：なし。

固定宇宙のκ-compact性は、数値λで切った空間圏の(κ,λ)-compact性と同じ対象・保存条件への比較がない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.smallKanObject_isKappaCompact`

:::

# 9.2.7 Finiteness Conditions on ∞-Categories

%%%
number := false
tag := "kerodon-9-2-7"
%%%

Kerodon [Tag 0685](https://kerodon.net/tag/0685)

:::definition "kerodon_9_2_7_1" (lean := "SSet.Finite, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence")
Kerodon Definition 9.2.7.1（[Tag 0686](https://kerodon.net/tag/0686)）。対応表の状態：本体にある。

*主張*　無限圏 $`C` は、有限単体集合 $`K` からの圏同値 $`K\to C` が存在するとき本質的に有限である。

同じ準圏Cについて∃K:SSet, K.Finiteかつ∃f:K⟶C, IsPrecompositionEquivalence fという既存の型の存在量化が原文の定義全体に一致する。有限模型にKan性を課さない。

:::

:::lemma_ "kerodon_9_2_7_2"
Kerodon Lemma 9.2.7.2（[Tag 0687](https://kerodon.net/tag/0687)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Kan 置換への有限な相対図式を、境界単射を備える有限模型とホモトピーで近似する型はある。本質的有限な任意の準圏 C に対して有限 K₀→K→C の厳密因数分解を作り、K→C を categorical equivalence とする型は見つからない。

:::

:::proposition "kerodon_9_2_7_3"
Kerodon Proposition 9.2.7.3（[Tag 0688](https://kerodon.net/tag/0688)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：辺の族の局所化の述語と有限写像円柱の始域射はある。有限の反転指定を付けた後も局所化が有限単体集合からの categorical equivalence を持つ型は見つからない。

:::

:::proposition "kerodon_9_2_7_4" (lean := "SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsPrecompositionEquivalence.isWeakHomotopyEquivalence, SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.isWeakHomotopyEquivalence_iff_isQCatEquivalence")
Kerodon Proposition 9.2.7.4（[Tag 0689](https://kerodon.net/tag/0689)）。対応表の状態：一部。

*主張*　Kan 複体 $`X` に対し、ある有限単体集合から $`X` への弱ホモトピー同値が存在することと、ある有限単体集合から $`X` への圏同値が存在することは同値である。

B6型照合：任意の前合成同値な単体写像は弱ホモトピー同値なので、有限 K を使う categorical equivalence から弱同値の証人が得られる。Kan 同士の Whitehead 型には K の Kan 性も必要で、任意の有限な弱同値模型から有限 categorical 模型を得る逆向きは残る。

:::

:::proposition "kerodon_9_2_7_6"
Kerodon Proposition 9.2.7.6（[Tag 068B](https://kerodon.net/tag/068B)）。対応表の状態：なし。

厳密SSet pushoutの有限性だけでは、原文のcategorical pushoutへの比較と本質的有限性を返さない。

宣言：`SerrePositivity.InfinityCategories.Project.FilteredExchange.finite_pushout`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence.of_isPushout_of_mono_other`

:::

:::corollary "kerodon_9_2_7_7"
Kerodon Corollary 9.2.7.7（[Tag 068D](https://kerodon.net/tag/068D)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常の単体集合の圏で有限個の有限単体集合を余極限すると有限になる。QC 内の有限図式で各準圏の本質的有限性がその余極限へ移る型は見つからない。

:::

:::proposition "kerodon_9_2_7_8"
Kerodon Proposition 9.2.7.8（[Tag 068E](https://kerodon.net/tag/068E)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：有限な単体集合の形状を境界の pushout で組む型はある。QC 内の Δ¹ の有限余極限閉包を本質的有限な準圏全体と同定する型は見つからない。

:::

:::proposition "kerodon_9_2_7_9"
Kerodon Proposition 9.2.7.9（[Tag 068G](https://kerodon.net/tag/068G)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：有限単体集合の通常圏での presentability と有限 Kan 置換の空間圏での compact 性はある。有限の categorical 模型を持つ準圏が QC の対象として compact になる型は見つからない。

:::

:::definition "kerodon_9_2_7_10"
Kerodon Definition 9.2.7.10（[Tag 068J](https://kerodon.net/tag/068J)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：準圏の頂点 retract と、写像の categorical equivalence の候補述語はある。QC の対象が本質的有限な準圏の h QCat 内の retract であることをまとめる述語は見つからない。

:::

:::proposition "kerodon_9_2_7_12"
Kerodon Proposition 9.2.7.12（[Tag 068L](https://kerodon.net/tag/068L)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：一般の compact 生成族の像の retract 判定と、その空間圏での適用はある。小さい準圏を QC の対象とし、本質的有限な準圏からの retract で判定する適用は見つからない。

:::

:::proposition "kerodon_9_2_7_13"
Kerodon Proposition 9.2.7.13（[Tag 06ET](https://kerodon.net/tag/06ET)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：有限単体集合由来の空間の小さい生成圏はある。QC の有限支配対象全体の小さい模型は見つからない。取得本文は ℵ₁-small の直後に有限個の単体と記しており、濃度の文言に差がある。

:::

:::proposition "kerodon_9_2_7_14"
Kerodon Proposition 9.2.7.14（[Tag 068N](https://kerodon.net/tag/068N)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：κ-small な通常の単体集合の presentability と空間圏の κ-small Kan 対象の compact 性はある。QC 内の Δ¹ の κ-small 余極限閉包、準圏の本質的小ささ、QC 内の κ-compact 性を結ぶ型は見つからない。

:::

:::proposition "kerodon_9_2_7_15"
Kerodon Proposition 9.2.7.15（[Tag 068P](https://kerodon.net/tag/068P)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：固定宇宙の空間圏で κ-small な Kan 対象を compact とする型と濃度変更の条件はある。λ-small 準圏の QC\_\{\<λ\} での (κ,λ)-compact 性と Δ¹ の生成閉包を往復する型は見つからない。

:::

# 9.2.8 Closure Properties of Compact Objects

%%%
number := false
tag := "kerodon-9-2-8"
%%%

Kerodon [Tag 06EU](https://kerodon.net/tag/06EU)

:::proposition "kerodon_9_2_8_1"
Kerodon Proposition 9.2.8.1（[Tag 06N0](https://kerodon.net/tag/06N0)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：点または辺からの coslice で compact 性を扱う補題はある。任意の (κ,λ)-finitary な右ファイブレーションで U(X) の相対 compact 性から X の相対 compact 性を導く型は見つからない。

:::

:::corollary "kerodon_9_2_8_2"
Kerodon Corollary 9.2.8.2（[Tag 06F4](https://kerodon.net/tag/06F4)）。対応表の状態：なし。

pointCosliceVertexは始点固定の矢印で、原文の終点図式固定のsliceとは逆向き。入力両端のcompact性も異なり、同じsliceの結論でない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.isKappaCompact_pointCosliceVertex`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.isKappaCompact_edgeCosliceVertex`

:::

:::proposition "kerodon_9_2_8_3" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.hasColimit_laxPullback_of_components, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isColimitCone_laxPullback_iff_components, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.exists_colimitCone_laxPullback_with_components") (uses := "kerodon_1_4_0_1, kerodon_7_1_9_5, kerodon_8_3_7_1")
Kerodon Proposition 9.2.8.3（[Tag 06EV](https://kerodon.net/tag/06EV)）。対応表の状態：一部。

*主張*　正則基数 $`\kappa\leq\lambda` に対し、$`(\kappa,\lambda)`-余完備な無限圏 $`C_-,C_+,C` と $`(\kappa,\lambda)`-finitary な関手 $`F_\pm:C_\pm\to C` を取る。向き付きファイバー積は $`(\kappa,\lambda)`-余完備で、両射影は $`(\kappa,\lambda)`-finitary である。対象 $`(x,y,F_-(x)\to F_+(y))` で $`x,y,F_-(x)` がそれぞれ $`(\kappa,\lambda)`-コンパクトなら、その対象も同じ意味でコンパクトである。

B6型照合：(1) の形だけ。lax pullback（= oriented fiber product, Fun(Δ¹,C) の strict pullback）で、両入力が余極限を持ち F± が保てば余極限が存在し、余極限錐は両射影で判定（任意の形状 J、(κ,λ) の制限なし）。(2) の compact 性の主張はない。名前空間 SerrePositivity.InfinityCategories.F2。

:::

:::corollary "kerodon_9_2_8_5" (uses := "kerodon_1_4_0_1, kerodon_7_1_9_7, kerodon_9_1_9_8, kerodon_9_2_8_3")
Kerodon Corollary 9.2.8.5（[Tag 06EX](https://kerodon.net/tag/06EX)）。対応表の状態：なし。

宇宙小のcompact性とstrict pullbackの定理は指定λ-small形状の(κ,λ)-compact性の主張に比較されていない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.componentCompactObjects_vertex_isKappaCompact`

:::

:::proposition "kerodon_9_2_8_6"
Kerodon Proposition 9.2.8.6（[Tag 06EZ](https://kerodon.net/tag/06EZ)）。対応表の状態：なし。

二脚pullbackのcompact性は原文の任意個の積の各因子のcompact性の判定と別対象。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isKappaCompact_pullback_of_components`

:::

:::corollary "kerodon_9_2_8_7"
Kerodon Corollary 9.2.8.7（[Tag 06F0](https://kerodon.net/tag/06F0)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：小さい通常圏の単体集合値極限と濃度つき filtered 余極限の交換、および Kan 複体の塔極限はある。二濃度で余完備な準圏の isofibration 塔で、成分の compact 性から極限準圏の compact 性を得る型は見つからない。

:::

:::proposition "kerodon_9_2_8_9"
Kerodon Proposition 9.2.8.9（[Tag 06F2](https://kerodon.net/tag/06F2)）。対応表の状態：なし。

定値一点図式のcompact性はあるが、原文の指定λ-smallだけをテストする条件との比較を持たない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.smallConstantPointDiagram_isKappaCompact`

:::

:::corollary "kerodon_9_2_8_11"
Kerodon Corollary 9.2.8.11（[Tag 06N1](https://kerodon.net/tag/06N1)）。対応表の状態：なし。

小準圏Aのcosliceにおける全κ-filtered余極限のcompact性は、原文の指定λ-smallのみでのcompact性と同じ型ではない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.isKappaCompact_smallSourceCosliceVertex`

:::

# 9.2.9 Compactness in ∞-Categories of Sections

%%%
number := false
tag := "kerodon-9-2-9"
%%%

Kerodon [Tag 06F5](https://kerodon.net/tag/06F5)

:::proposition "kerodon_9_2_9_1"
Kerodon Proposition 9.2.9.1（[Tag 06F6](https://kerodon.net/tag/06F6)）。対応表の状態：なし。

strict pullbackのcompact性は原文の指定QC\_\<μ内のκ-small図式の極限との比較がなく、二濃度compact性も異なる。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isKappaCompact_pullback_of_components`

:::

:::corollary "kerodon_9_2_9_2"
Kerodon Corollary 9.2.9.2（[Tag 06F7](https://kerodon.net/tag/06F7)）。対応表の状態：なし。

引用は非可算μ-compact性についての型で、原文の有限図式でのℵ0-compact性を返さない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isKappaCompact_pullback_of_components`

:::

:::definition "kerodon_9_2_9_4"
Kerodon Definition 9.2.9.4（[Tag 06F9](https://kerodon.net/tag/06F9)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：単独の準圏の小 κ-filtered 余極限と指定二脚の引き戻しでの存在はある。内ファイブレーションを任意の Δⁿ 上に引き戻し、全ての引き戻しに (κ,λ)-余完備性を課す述語は見つからない。

:::

:::definition "kerodon_9_2_9_5"
Kerodon Variant 9.2.9.5（[Tag 06FA](https://kerodon.net/tag/06FA)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：ordinal nerve の κ-filtered 性と自然数列から可算形状の保存余極限を得る型はある。任意の Δⁿ への引き戻しで κ-順次余極限を要求する定義、および (κ,κ⁺)-余完備性との同一視は見つからない。

:::

:::proposition "kerodon_9_2_9_7"
Kerodon Proposition 9.2.9.7（[Tag 06FC](https://kerodon.net/tag/06FC)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：相対余極限性と小さい κ-filtered 余極限存在の述語はある。Δ¹ 上への引き戻しごとの二濃度余完備性と、頂点上の全余極限が edgewise となる条件との三条件の iff は見つからない。

:::

:::proposition "kerodon_9_2_9_14"
Kerodon Proposition 9.2.9.14（[Tag 06FK](https://kerodon.net/tag/06FK)）。対応表の状態：なし。

全関手圏内のcompact性は原文のΔ1上の指定section準圏のcompact性と別の対象。比較を含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.isKappaCompact_functorVertex_of_endFamily`

:::

:::proposition "kerodon_9_2_9_16"
Kerodon Proposition 9.2.9.16（[Tag 06FM](https://kerodon.net/tag/06FM)）。対応表の状態：なし。

全関手圏のcompact性は原文のUのsection準圏におけるcompact性を直接返さない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.isKappaCompact_functorVertex_of_endFamily`

:::

:::corollary "kerodon_9_2_9_19"
Kerodon Corollary 9.2.9.19（[Tag 06FQ](https://kerodon.net/tag/06FQ)）。対応表の状態：なし。

全関手圏のcompact性はcocartesian sectionの全部分圏への同じcompact性に移す比較がない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.isKappaCompact_functorVertex_of_endFamily`

:::

