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

原文はXの部分単体集合が別の部分単体集合と余積分解するというsummandの述語。summand/componentSubcomplex/成分因子化を再検索。成分類の逆像の部分複体はあるが、その包含をsummandとする条件/分解そのものの宣言ではない。

:::

:::definition "kerodon_1_2_1_6" (lean := "SSet.IsConnected")
Kerodon Definition 1.2.1.6（[Tag 00GB](https://kerodon.net/tag/00GB)）。対応表の状態：Mathlib にある。

仮定：単体集合 S（Kerodon と一致）。結論：原文の非空かつ非自明な直和因子を持たない条件に対応する IsConnected は、成分集合 S.π₀ が非空かつ高々一元であること（一致）。

:::

:::definition "kerodon_1_2_1_8"
Kerodon Definition 1.2.1.8（[Tag 00GD](https://kerodon.net/tag/00GD)）。対応表の状態：なし。

原文は連結な直和成分としての部分単体集合と、その全体の集合を定義する。SSet.π₀ は辺の同値関係による頂点の商集合であり、この部分複体/直和成分の条件を型で与えない。二つのモデルの比較は追加の議論。

宣言：`SSet.π₀`

:::

:::proposition "kerodon_1_2_1_11"
Kerodon Proposition 1.2.1.11（[Tag 00GG](https://kerodon.net/tag/00GG)）。対応表の状態：なし。

原文は連結なSからTへの写像の像を含む一意な連結な直和成分。componentSubcomplexと成分因子化を再検索し、選んだπ₀の部分集合の逆像の型を確認した。像を含む連結summandの一意性を返す型は見つからない。

:::

:::corollary "kerodon_1_2_1_12"
Kerodon Corollary 1.2.1.12（[Tag 00GH](https://kerodon.net/tag/00GH)）。対応表の状態：なし。

原文は連結性と全てのIについての指定定数写像 I→Hom(S,const I) の全単射の iff。homEquiv は別の Hom と関数集合の同値、isConnected\_iff\_nonempty\_unique は π₀ の一意性との iff。指定写像の像と Hom 同値を結んで関数集合の判定を行う追加議論が必要で、いずれの方向も引用型が直接返すものではない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.homEquiv`、`SSet.isConnected_iff_nonempty_unique`

:::

:::proposition "kerodon_1_2_1_13"
Kerodon Proposition 1.2.1.13（[Tag 00GJ](https://kerodon.net/tag/00GJ)）。対応表の状態：なし。

原文は S 自体の連結成分による余積分解。componentSubcomplex と componentClassEquiv は成分類の述語で選んだ部分複体のπ₀を計算するだけで、Sへの余積比較の同型を返さない。対象分解の証明の部品とする。

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

原文は π₀⊣const とその指定単位の構成。homEquiv の型 (X→discrete T)≃(π₀X→T) はこの随伴の Hom 同値成分を逆向きにしたものを直接与える。自然性・指定単位まで完成した Adjunction の宣言とせず、構成のこの成分に限定する。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.homEquiv`

:::

:::proposition "kerodon_1_2_1_22"
Kerodon Proposition 1.2.1.22（[Tag 00GT](https://kerodon.net/tag/00GT)）。対応表の状態：Mathlib にある。

仮定：単体集合 S（Kerodon と一致）。結論：isColimitCoforkπ₀ は S.π₀ を 1 単体の二つの面 d₀,d₁ : S₁ → S₀ の余等化子として与える（一致）。

宣言：`SSet.isColimitCoforkπ₀`

:::

:::definition "kerodon_1_2_1_24"
Kerodon Variant 1.2.1.24（[Tag 00GV](https://kerodon.net/tag/00GV)）。対応表の状態：なし。

原文は非退化辺だけのd₀,d₁の余等化子がπ₀であるという指定cofork。MathlibのisColimitCoforkπ₀は全ての辺を使う別のcofork。非退化辺・coequalizer・coforkを再検索したが、退化辺の除去を実装する同じ比較は見つからず追加議論を要する。

:::

:::corollary "kerodon_1_2_1_25"
Kerodon Corollary 1.2.1.25（[Tag 050A](https://kerodon.net/tag/050A)）。対応表の状態：なし。

原文は全n≥2について∂Δnの連結性。boundaryとconnectedを再検索。KSTのboundaryReducedRealization\_isConnectedはS構成の全零境界商、他のboundary connectingは連結準同型であり、標準単体の境界の連結性ではない。

:::

:::proposition "kerodon_1_2_1_26"
Kerodon Proposition 1.2.1.26（[Tag 00GW](https://kerodon.net/tag/00GW)）。対応表の状態：なし。

原文は連結な単体集合の有限積閉性。IsConnected.prod・π₀とprodを再検索。CategoryTheory.IsConnected.prodは通常圏の連結性、KanKernelPairPiZeroLoopEquiv\_productは特定のloop/kernel pairの式であり、SSet.IsConnectedの同じ有限積についての結論ではない。

:::

:::corollary "kerodon_1_2_1_27"
Kerodon Corollary 1.2.1.27（[Tag 00GX](https://kerodon.net/tag/00GX)）。対応表の状態：なし。

原文はSSet.π₀Functorの有限積保存。π₀/piZero/productの再検索で、Kan置換や特定loopの比較は見つかるが、任意SSetのπ₀(X×Y)→π₀X×π₀Yという指定比較射の全単射/同型ではない。

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
Kerodon Definition 1.2.3.1（[Tag 001Y](https://kerodon.net/tag/001Y)）。対応表の状態：なし。

原文は指定u:S→Sing(Y)が全Xへの合成写像の全単射を満たすという任意Y,uの普遍性の述語。toTop と sSetTopAdj は標準の実現関手と随伴で、任意の指定uに対するその条件の定義ではない。標準単位の例と任意のuの述語を同一視しない。

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

原文は標準単体の下方閉な面族Uに対応する部分単体集合と台条件の位相部分空間を同時に構成する。toTop/Subcomplex/lowerSet/simplexで再検索。一般の部分複体やorder idealはあるが、このUからの二つの指定対象の構成は見つからない。

:::

:::proposition "kerodon_1_2_3_10"
Kerodon Proposition 1.2.3.10（[Tag 0028](https://kerodon.net/tag/0028)）。対応表の状態：なし。

原文は下方閉な面族Uに対する単体部分複体からSing(台条件の部分空間)への指定比較が実現の普遍性を持つ。toTopとSubcomplex・lowerSetを再検索。標準単体全体のtoTopSimplexだけでは、任意Uへのこの制限射と普遍性を直接結論しない。

:::

:::lemma_ "kerodon_1_2_3_13"
Kerodon Lemma 1.2.3.13（[Tag 00H2](https://kerodon.net/tag/00H2)）。対応表の状態：なし。

原文は任意の充満部分圏Uが単射沿いのpushout・単射列の余極限・単体の全余積で閉じれば全SSetを含むという帰納原理。induction/Subcomplex/relativeCellComplexOfMonoで再検索。相対セル分解は帰納原理の証明材料であり、このUへの所属を直接返す型ではない。

:::

:::proposition "kerodon_1_2_3_15" (lean := "CategoryTheory.Presheaf.uliftYonedaAdjunction")
Kerodon Proposition 1.2.3.15（[Tag 002F](https://kerodon.net/tag/002F)）。対応表の状態：Mathlib にある。

仮定：余単体対象 Q と小余極限を持つ圏 C（Lean が弱い：uliftYonedaAdjunction には Q の必要な左 Kan 拡張があればよい）。結論：Q による制限 Yoneda、すなわち \[n\]↦ULift (Qₙ ⟶ X) の左随伴を与える（一致）。

:::

:::proposition "kerodon_1_2_3_18"
Kerodon Proposition 1.2.3.18（[Tag 00H5](https://kerodon.net/tag/00H5)）。対応表の状態：なし。

原文は任意Sの実現の弧状連結性・連結性・Sの連結性の3条件同値。toTopとConnected/π₀で再検索。標準位相単体だけの連結性や標準単体の弱同値は、任意Sの指定実現の同値の方向ではない。

:::

:::corollary "kerodon_1_2_3_19"
Kerodon Corollary 1.2.3.19（[Tag 00H6](https://kerodon.net/tag/00H6)）。対応表の状態：なし。

原文は任意Sのπ₀と実現の位相的π₀の標準全単射。toTopとπ₀/componentを再検索。標準単体の位相的連結性とSSet側のπ₀の普遍性はあるが、両者を結ぶこの同じ比較写像は見つからない。

:::

# 1.2.4 Horns

%%%
number := false
tag := "kerodon-1-2-4"
%%%

Kerodon [Tag 000K](https://kerodon.net/tag/000K)

*定義 1.6 （面 $`\partial_j\Delta^n`$）*

$`0\le j\le n`$ について、$`\Delta^n`$ の部分単体的集合 $`\partial_j\Delta^n`$ を

$$`\partial_j\Delta^n([m])=\{\theta\colon[m]\to[n]\mid j\notin\theta([m])\}`$$

で定め、$`\Delta^n`$ の $`j`$ 番目の面という。

:::definition "kerodon_1_2_4_1" (lean := "SSet.horn")
Kerodon Construction 1.2.4.1（[Tag 000U](https://kerodon.net/tag/000U)）。対応表の状態：Mathlib にある。

仮定：n\>0 と i : Fin (n+1)（Lean が弱い：horn の定義自体は n=0 にも適用できる）。結論：horn n i は Δ\[n\] の i 番以外の面の和。原文の像が i 以外の頂点を一つ欠くという条件と同じ部分複体（一致）。

*定義 1.7 （horn $`\Lambda^n_i`$）*

$`n\ge1`$、$`0\le i\le n`$ とする。$`\Delta^n`$ の部分単体的集合 $`\Lambda^n_i`$ を、次のどちらかの書き方で定める。

1. \*\*部分単体的集合として直接\*\*：$`\Lambda^n_i([m])=\{\theta\colon[m]\to[n]\mid\theta([m])\cup\{i\}\ne[n]\}`$。

2. \*\*面の和として\*\*：$`\Lambda^n_i=\bigcup_{j\ne i}\partial_j\Delta^n`$。

両者は一致する。$`\theta([m])\cup\{i\}\ne[n]`$ は、$`\theta([m])`$ に含まれない $`j\ne i`$ があること、つまりある $`j\ne i`$ について $`\theta\in\partial_j\Delta^n([m])`$ であることと同じだからである。

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

*注意 （一点への射）*

$`\Delta^0`$ は各段が一点の単体的集合で、任意の単体的集合 $`X`$ から唯一の射 $`X\to\Delta^0`$ がある。$`X`$ が quasicategory（定義 1.8）であることは $`X\to\Delta^0`$ が inner fibration であることと、Kan 複体（定義 1.9）であることは $`X\to\Delta^0`$ が Kan fibration であることと同じである。

:::definition "kerodon_1_2_5_1" (lean := "SSet.KanComplex, SSet.KanComplex.hornFilling, SSet.KanComplex.iff")
Kerodon Definition 1.2.5.1（[Tag 002H](https://kerodon.net/tag/002H)）。対応表の状態：Mathlib にある。

仮定：単体集合 X（Kerodon と一致）。結論：KanComplex.iff は KanComplex X と、全ての正次数で内外の別なく任意のホーンが Δ\[n\] へ延長できることの同値（一致）。

*定義 1.9 （Kan 複体）*

単体的集合 $`X`$ が Kan 複体であるとは、すべての $`0\le i\le n`$ について、任意の射 $`\Lambda^n_i\to X`$ が $`\Delta^n\to X`$ に延長できることをいう。

:::

:::proposition "kerodon_1_2_5_8"
Kerodon Proposition 1.2.5.8（[Tag 002K](https://kerodon.net/tag/002K)）。対応表の状態：なし。

原文は全位相空間XのSing(X)のKan性。現本体全体・MathlibをtoSSet/singular/Kanで再検索。MathlibのSingularSet・KanComplexのTODOと、別のcompatible input unionのtoSSetはあるが、位相空間のsingular setのKan instanceは見つからない。

:::

:::proposition "kerodon_1_2_5_9"
Kerodon Proposition 1.2.5.9（[Tag 00MG](https://kerodon.net/tag/00MG)）。対応表の状態：一部。

原文は全単体群の台がKan。ringSpace\_kanComplex の型は単体的環 A の台のKan性であり、その加法単体群へ対象を限定した同じ結論を直接与える。全単体群への拡張は数えない。

宣言：`SerrePositivity.KST.Comparison.ringSpace_kanComplex`

:::

:::proposition "kerodon_1_2_5_10" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromTopologicalSpacesToSimplicialSets.KanHomotopyZero.mk_eq_iff, SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromTopologicalSpacesToSimplicialSets.ZeroRelations.equivalence, SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero, SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.equivPiZero")
Kerodon Proposition 1.2.5.10（[Tag 00HC](https://kerodon.net/tag/00HC)）。対応表の状態：本体にある。

仮定：Kan 複体 X と二頂点（Kerodon と一致）。結論：KanHomotopyZero.mk\_eq\_iff は頂点類の一致と RelStruct₀ の存在を同値とし、RelStruct₀ は指定方向の辺、equivPiZero は成分類との比較を与える（一致）。

:::

:::corollary "kerodon_1_2_5_11"
Kerodon Corollary 1.2.5.11（[Tag 00HD](https://kerodon.net/tag/00HD)）。対応表の状態：なし。

原文は任意集合添字のKan積のπ₀の指定比較の全単射。π₀/piZero/product・IsConnected.prodを再検索。二項loop/kernel pairの成分式や通常圏の積連結性は異なる対象の主張で、この任意積の比較ではない。

:::

