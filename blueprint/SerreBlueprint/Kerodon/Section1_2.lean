import Verso
import VersoManual
import VersoBlueprint
import Mathlib.AlgebraicTopology.SimplicialSet.Horn
import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits
import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex
import Mathlib.AlgebraicTopology.SimplicialSet.PiZero
import Mathlib.AlgebraicTopology.SingularSet
import Mathlib.AlgebraicTopology.TopologicalSimplex
import Mathlib.CategoryTheory.Limits.Presheaf
import SerrePositivity.HomotopicalAlgebra.Simplicial.PiZeroLocalization
import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.HomotopyDegreeZero
import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromTopologicalSpacesToSimplicialSets.HomotopyZeroRelations
import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.PiZeroConstant

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "1.2 From Topological Spaces to Simplicial Sets" =>
%%%
number := false
tag := "kerodon-1-2"
%%%

Kerodon の 1.2 節（[Tag 0508](https://kerodon.net/tag/0508)）の項目と、SerrePositivity・Mathlib の宣言との対応。本文は対応表（research/kerodon-coverage）の判定の理由の要約で、Kerodon の本文の写しではない。

# 1.2.1 Connected Components of Simplicial Sets

%%%
number := false
tag := "kerodon-1-2-1"
%%%

Kerodon [Tag 00G5](https://kerodon.net/tag/00G5)

:::definition "kerodon_1_2_1_1"
Kerodon Definition 1.2.1.1（[Tag 00G6](https://kerodon.net/tag/00G6)）。対応表の状態：なし。

確認済み・なし（対象ソースの探索範囲内）。summandと直和成分の命名・定義を検索。一般の余積のsummandに関する記載は別物で、部分単体集合が直和成分であるという述語は見つからない。

:::

:::definition "kerodon_1_2_1_6" (lean := "SSet.IsConnected")
Kerodon Definition 1.2.1.6（[Tag 00GB](https://kerodon.net/tag/00GB)）。対応表の状態：Mathlib にある。

仮定：単体集合 S（Kerodon と一致）。結論：原文の非空かつ非自明な直和因子を持たない条件に対応する IsConnected は、成分集合 S.π₀ が非空かつ高々一元であること（一致）。

:::

:::definition "kerodon_1_2_1_8"
Kerodon Definition 1.2.1.8（[Tag 00GD](https://kerodon.net/tag/00GD)）。対応表の状態：一部。

π₀は辺の関係で頂点を商にした集合。連結な直和成分そのものとしての部分複体の定義ではない。

宣言：`SSet.π₀`

:::

:::proposition "kerodon_1_2_1_11"
Kerodon Proposition 1.2.1.11（[Tag 00GG](https://kerodon.net/tag/00GG)）。対応表の状態：なし。

確認済み・なし（対象ソースの探索範囲内）。連結な源の像・成分への因子化を検索。componentSubcomplexと局所化後のcomponentsFactorizationはあるが、像の入る一意な連結成分の定理は見つからない。

:::

:::corollary "kerodon_1_2_1_12"
Kerodon Corollary 1.2.1.12（[Tag 00GH](https://kerodon.net/tag/00GH)）。対応表の状態：一部。

homEquivとπ₀のUniqueによる連結性の特徴づけは材料。任意のIについて原文の標準写像が全単射であるという一括の同値は引用されていない。homEquivの名前空間を補正。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.homEquiv`、`SSet.isConnected_iff_nonempty_unique`

:::

:::proposition "kerodon_1_2_1_13"
Kerodon Proposition 1.2.1.13（[Tag 00GJ](https://kerodon.net/tag/00GJ)）。対応表の状態：一部。

成分の集合で指定した部分複体とそのπ₀との全単射はある。S全体の余積分解の宣言ではない。PiZeroConstant.homEquivの名前空間を補正。

宣言：`SerrePositivity.KST.Comparison.componentSubcomplex`、`SerrePositivity.KST.Comparison.componentClassEquiv`、`SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.homEquiv`

:::

:::corollary "kerodon_1_2_1_14"
Kerodon Corollary 1.2.1.14（[Tag 00GK](https://kerodon.net/tag/00GK)）。対応表の状態：Mathlib にある。

仮定：単体集合 S（Kerodon と一致）。結論：π₀.nonempty\_iff は成分集合の非空性と頂点集合の非空性の同値であり、空性の同値を逆に表す（一致）。

宣言：`SSet.π₀.nonempty_iff`

:::

:::corollary "kerodon_1_2_1_15" (lean := "SSet.isConnected_iff_nonempty_unique")
Kerodon Corollary 1.2.1.15（[Tag 00GL](https://kerodon.net/tag/00GL)）。対応表の状態：Mathlib にある。

仮定：単体集合 S（Kerodon と一致）。結論：isConnected\_iff\_nonempty\_unique は S の連結性と成分集合にちょうど一元があることの同値（一致）。

:::

:::definition "kerodon_1_2_1_18" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.component, SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.fromComponents")
Kerodon Construction 1.2.1.18（[Tag 00GP](https://kerodon.net/tag/00GP)）。対応表の状態：本体にある。

仮定：単体集合 S（Kerodon と一致）。結論：component は各次数の単体の成分を返し、fromComponents に S.π₀ の恒等写像を与えると定数単体集合への成分写像になる（一致）。

:::

:::proposition "kerodon_1_2_1_19" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.homEquiv, SerrePositivity.SimplicialModel.PiZeroLocalization.classEquiv")
Kerodon Proposition 1.2.1.19（[Tag 00GQ](https://kerodon.net/tag/00GQ)）。対応表の状態：本体にある。

仮定：単体集合 S と集合 J（Kerodon と一致）。結論：homEquiv の逆写像は成分から J への関数を成分写像と合成し、S ⟶ discrete J との全単射を与える（一致）。

:::

:::corollary "kerodon_1_2_1_21"
Kerodon Corollary 1.2.1.21（[Tag 00GS](https://kerodon.net/tag/00GS)）。対応表の状態：一部。

Homの全単射はあるが、π₀Functorと定数関手のAdjunctionとして組み立てた宣言は引用されていない。homEquivの名前空間を補正。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.homEquiv`

:::

:::proposition "kerodon_1_2_1_22"
Kerodon Proposition 1.2.1.22（[Tag 00GT](https://kerodon.net/tag/00GT)）。対応表の状態：Mathlib にある。

仮定：単体集合 S（Kerodon と一致）。結論：isColimitCoforkπ₀ は S.π₀ を 1 単体の二つの面 d₀,d₁ : S₁ → S₀ の余等化子として与える（一致）。

宣言：`SSet.isColimitCoforkπ₀`

:::

:::definition "kerodon_1_2_1_24"
Kerodon Variant 1.2.1.24（[Tag 00GV](https://kerodon.net/tag/00GV)）。対応表の状態：なし。

確認済み・なし（対象ソースの探索範囲内）。非退化辺・余等化子・coforkを検索。PiZeroの全ての辺によるcoforkはあるが、非退化辺だけの版は見つからない。

:::

:::corollary "kerodon_1_2_1_25"
Kerodon Corollary 1.2.1.25（[Tag 050A](https://kerodon.net/tag/050A)）。対応表の状態：なし。

確認済み・なし（対象ソースの探索範囲内）。境界と連結性を検索。KSTのboundaryReducedRealizationはS構成の対象であり、標準単体の境界∂Δⁿの連結性の定理ではない。

:::

:::proposition "kerodon_1_2_1_26"
Kerodon Proposition 1.2.1.26（[Tag 00GW](https://kerodon.net/tag/00GW)）。対応表の状態：なし。

確認済み・なし（対象ソースの探索範囲内）。連結性の積とπ₀の積を検索。通常圏の連結性の積、Kanの積の充填性、特殊なloop積の成分公式はあるが、一般SSetの連結性の有限積閉性は見つからない。

:::

:::corollary "kerodon_1_2_1_27"
Kerodon Corollary 1.2.1.27（[Tag 00GX](https://kerodon.net/tag/00GX)）。対応表の状態：なし。

確認済み・なし（対象ソースの探索範囲内）。π₀Functorの有限積保存、piZero/product/connectedを検索。Kan置換の有限積比較のπ₀全単射は、π₀(X×Y)とπ₀X×π₀Yの比較ではない。対応する一般定理は見つからない。

:::

# 1.2.2 The Singular Simplicial Set of a Topological Space

%%%
number := false
tag := "kerodon-1-2-2"
%%%

Kerodon [Tag 001Q](https://kerodon.net/tag/001Q)

:::definition "kerodon_1_2_2_1" (lean := "SimplexCategory.toTop")
Kerodon Notation 1.2.2.1（[Tag 050B](https://kerodon.net/tag/050B)）。対応表の状態：Mathlib にある。

仮定：非負整数 n と位相空間 X（Kerodon と一致。Lean では SimplexCategory の \[n\] を評価する）。結論：SimplexCategory.toTop の n 次の値は非負実座標の和が 1 の部分空間。X への連続写像が特異 n 単体となる（一致）。

:::

:::definition "kerodon_1_2_2_2" (lean := "TopCat.toSSet, TopCat.toSSetObjEquiv")
Kerodon Construction 1.2.2.2（[Tag 001R](https://kerodon.net/tag/001R)）。対応表の状態：Mathlib にある。

仮定：位相空間 X と非負次数 n（Kerodon と一致）。結論：toSSetObjEquiv は TopCat.toSSet.obj X の n 単体を位相的標準 n 単体から X への連続写像と同定する。順序写像の作用は連続写像による前合成（一致）。

:::

:::definition "kerodon_1_2_2_8" (lean := "CategoryTheory.Presheaf.restrictedULiftYoneda")
Kerodon Variant 1.2.2.8（[Tag 001T](https://kerodon.net/tag/001T)）。対応表の状態：Mathlib にある。

仮定：圏 C の余単体対象 Q と対象 X（Lean が弱い：restrictedULiftYoneda は任意の添字圏の関手 Q に適用できる）。結論：Δᵒᵖ の \[n\] に ULift (Qₙ ⟶ X) を割り当て、写像に Q の像で前合成する（一致。ULift は宇宙調整）。

:::

# 1.2.3 The Geometric Realization of a Simplicial Set

%%%
number := false
tag := "kerodon-1-2-3"
%%%

Kerodon [Tag 001X](https://kerodon.net/tag/001X)

:::definition "kerodon_1_2_3_1"
Kerodon Definition 1.2.3.1（[Tag 001Y](https://kerodon.net/tag/001Y)）。対応表の状態：一部。

toTopと随伴は実現の構成。任意の指定uがYを実現として示すという述語は引用されていない。

宣言：`SSet.toTop`、`sSetTopAdj`

:::

:::definition "kerodon_1_2_3_3" (lean := "SSet.toTop")
Kerodon Notation 1.2.3.3（[Tag 0020](https://kerodon.net/tag/0020)）。対応表の状態：Mathlib にある。

仮定：単体集合 S（Lean が弱い：幾何学的実現の存在は sSetTopAdj が与える）。結論：SSet.toTop.obj S が関手的に選んだ実現で、scoped\[Simplicial\] の絶対値記法がこれを指す（一致）。

:::

:::proposition "kerodon_1_2_3_4" (lean := "sSetTopAdj")
Kerodon Proposition 1.2.3.4（[Tag 0021](https://kerodon.net/tag/0021)）。対応表の状態：Mathlib にある。

仮定：任意の単体集合 S（Kerodon と一致）。結論：sSetTopAdj の単位 S ⟶ TopCat.toSSet.obj (SSet.toTop.obj S) と随伴の Hom 全単射が、実現の存在とその普遍性を与える（一致）。

:::

:::corollary "kerodon_1_2_3_5" (lean := "sSetTopAdj")
Kerodon Corollary 1.2.3.5（[Tag 0022](https://kerodon.net/tag/0022)）。対応表の状態：Mathlib にある。

仮定：単体集合の圏と位相空間の圏（Kerodon と一致）。結論：sSetTopAdj : SSet.toTop ⊣ TopCat.toSSet は特異単体集合の左随伴を幾何学的実現として与える（一致）。

:::

:::lemma_ "kerodon_1_2_3_6" (lean := "sSetTopAdj")
Kerodon Lemma 1.2.3.6（[Tag 0023](https://kerodon.net/tag/0023)）。対応表の状態：Mathlib にある。

仮定：小さい図式 S : J ⥤ SSet と各 S(j) の実現（Lean が弱い：存在は sSetTopAdj により一律に与えられる）。結論：左随伴 SSet.toTop の余極限保存により colim S の実現は各 S(j) の実現の余極限（一致。引用型はこの保存を与える随伴）。

:::

:::definition "kerodon_1_2_3_7"
Kerodon Notation 1.2.3.7（[Tag 0024](https://kerodon.net/tag/0024)）。対応表の状態：なし。

確認済み・なし（対象ソースの探索範囲内）。下方閉集合・標準単体の部分複体・台による位相部分空間を検索。一般のfaceや部分複体の構成はあるが、原文の組み合わされた構成は見つからない。

:::

:::proposition "kerodon_1_2_3_10"
Kerodon Proposition 1.2.3.10（[Tag 0028](https://kerodon.net/tag/0028)）。対応表の状態：なし。

確認済み・なし（対象ソースの探索範囲内）。前項の下方閉集合と位相的実現を検索。標準単体全体の実現同型はあるが、任意の下方閉な面集合への制限版は見つからない。

:::

:::lemma_ "kerodon_1_2_3_13"
Kerodon Lemma 1.2.3.13（[Tag 00H2](https://kerodon.net/tag/00H2)）。対応表の状態：なし。

確認済み・なし（対象ソースの探索範囲内）。SSetの押し出し・列余極限・単体の余積による帰納原理を検索。相対セル分解と有限posetのlower-set帰納法は材料・別の限定された主張で、原文の一般帰納原理は見つからない。

:::

:::proposition "kerodon_1_2_3_15" (lean := "CategoryTheory.Presheaf.uliftYonedaAdjunction")
Kerodon Proposition 1.2.3.15（[Tag 002F](https://kerodon.net/tag/002F)）。対応表の状態：Mathlib にある。

仮定：余単体対象 Q と小余極限を持つ圏 C（Lean が弱い：uliftYonedaAdjunction には Q の必要な左 Kan 拡張があればよい）。結論：Q による制限 Yoneda、すなわち \[n\]↦ULift (Qₙ ⟶ X) の左随伴を与える（一致）。

:::

:::proposition "kerodon_1_2_3_18"
Kerodon Proposition 1.2.3.18（[Tag 00H5](https://kerodon.net/tag/00H5)）。対応表の状態：なし。

確認済み・なし（対象ソースの探索範囲内）。toTop・実現と連結性・弧状連結性を検索。標準単体の弧状連結性とKSTの特殊な実現のSSet連結性はあるが、任意SSetについての3条件の同値は見つからない。

:::

:::corollary "kerodon_1_2_3_19"
Kerodon Corollary 1.2.3.19（[Tag 00H6](https://kerodon.net/tag/00H6)）。対応表の状態：なし。

確認済み・なし（対象ソースの探索範囲内）。toTopとπ₀・連結成分を検索。任意SSetのπ₀と位相的実現のπ₀の自然な全単射は見つからない。

:::

# 1.2.4 Horns

%%%
number := false
tag := "kerodon-1-2-4"
%%%

Kerodon [Tag 000K](https://kerodon.net/tag/000K)

:::definition "kerodon_1_2_4_1" (lean := "SSet.horn")
Kerodon Construction 1.2.4.1（[Tag 000U](https://kerodon.net/tag/000U)）。対応表の状態：Mathlib にある。

仮定：n\>0 と i : Fin (n+1)（Lean が弱い：horn の定義自体は n=0 にも適用できる）。結論：horn n i は Δ\[n\] の i 番以外の面の和。原文の像が i 以外の頂点を一つ欠くという条件と同じ部分複体（一致）。

:::

:::proposition "kerodon_1_2_4_7" (lean := "SSet.horn.IsCompatible, SSet.horn.IsCompatible.desc, SSet.horn.hom_ext")
Kerodon Proposition 1.2.4.7（[Tag 050F](https://kerodon.net/tag/050F)）。対応表の状態：Mathlib にある。

仮定：単体集合 X と n\>0、i : Fin (n+1)（Kerodon と一致。Lean はホーンの次元を n+1 と書く）。結論：IsCompatible が面同士の整合条件、desc がその族からの延長、hom\_ext が面への制限の単射性を与える（一致）。

:::

# 1.2.5 Kan Complexes

%%%
number := false
tag := "kerodon-1-2-5"
%%%

Kerodon [Tag 002G](https://kerodon.net/tag/002G)

:::definition "kerodon_1_2_5_1" (lean := "SSet.KanComplex, SSet.KanComplex.hornFilling, SSet.KanComplex.iff")
Kerodon Definition 1.2.5.1（[Tag 002H](https://kerodon.net/tag/002H)）。対応表の状態：Mathlib にある。

仮定：単体集合 X（Kerodon と一致）。結論：KanComplex.iff は KanComplex X と、全ての正次数で内外の別なく任意のホーンが Δ\[n\] へ延長できることの同値（一致）。

:::

:::proposition "kerodon_1_2_5_8"
Kerodon Proposition 1.2.5.8（[Tag 002K](https://kerodon.net/tag/002K)）。対応表の状態：なし。

確認済み・なし（対象ソースの探索範囲内）。toSSet・singularとKanComplexを検索。MathlibのKanComplexおよびSingularSetにTODOとして残り、自前の該当定理も見つからない。

:::

:::proposition "kerodon_1_2_5_9"
Kerodon Proposition 1.2.5.9（[Tag 00MG](https://kerodon.net/tag/00MG)）。対応表の状態：一部。

ringSpace\_kanComplexは単体的環の台単体集合に限定した特例。一般の単体群の定理としては扱わない。

宣言：`SerrePositivity.KST.Comparison.ringSpace_kanComplex`

:::

:::proposition "kerodon_1_2_5_10" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromTopologicalSpacesToSimplicialSets.KanHomotopyZero.mk_eq_iff, SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromTopologicalSpacesToSimplicialSets.ZeroRelations.equivalence, SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero, SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.equivPiZero")
Kerodon Proposition 1.2.5.10（[Tag 00HC](https://kerodon.net/tag/00HC)）。対応表の状態：本体にある。

仮定：Kan 複体 X と二頂点（Kerodon と一致）。結論：KanHomotopyZero.mk\_eq\_iff は頂点類の一致と RelStruct₀ の存在を同値とし、RelStruct₀ は指定方向の辺、equivPiZero は成分類との比較を与える（一致）。

:::

:::corollary "kerodon_1_2_5_11"
Kerodon Corollary 1.2.5.11（[Tag 00HD](https://kerodon.net/tag/00HD)）。対応表の状態：なし。

確認済み・なし（対象ソースの探索範囲内）。Kanの積とπ₀の比較を検索。高次ホモトピー群の二項積の単射とloop積の公式はあるが、任意集合添字のKan積のπ₀の全単射は見つからない。

:::

