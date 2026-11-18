import Verso
import VersoManual
import VersoBlueprint
import Mathlib.AlgebraicTopology.Quasicategory.Basic
import Mathlib.AlgebraicTopology.Quasicategory.InnerFibration
import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
import Mathlib.AlgebraicTopology.SimplicialSet.NerveAdjunction
import Mathlib.CategoryTheory.CommSq
import Mathlib.CategoryTheory.LiftingProperties.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.MorphismProperty.Retract
import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition
import Mathlib.CategoryTheory.Retract
import Mathlib.CategoryTheory.SmallObject.TransfiniteCompositionLifting
import SerrePositivity.HomotopicalAlgebra.Simplicial.Generators
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.Terminal
import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.CompositionTriangleSpace
import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.ContractibleKan
import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.FunctorCategory
import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.InnerAnodyneEquivalence
import SerrePositivity.KST.Fibration.CoreFactorization
import SerrePositivity.KST.SConstruction.STrivialFibration

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "1.5 Functors of ∞-Categories" =>
%%%
number := false
tag := "kerodon-1-5"
%%%

Kerodon の 1.5 節（[Tag 0055](https://kerodon.net/tag/0055)）の項目と、SerrePositivity・Mathlib の宣言との対応。本文は対応表（research/kerodon-coverage）の判定の理由の要約で、Kerodon の本文の写しではない。

*定義 5.3 （fibration）*

単体的集合の射 $`q\colon E\to B` が、次の表の包含のすべてに対して右持ち上げ性質（定義 5.2）をもつとき、それぞれ次のように呼ぶ（horn は定義 1.7）。

:::definition "kerodon_1_5_0_1" (lean := "SSet, SSet.Quasicategory")
Kerodon Definition 1.5.0.1（[Tag 0056](https://kerodon.net/tag/0056)）。対応表の状態：Mathlib にある。

仮定：二つの準圏 C,D（Kerodon と一致）。結論：SSet での射 C ⟶ D が原文の関手。Quasicategory が両端の条件で、射には追加データがない（一致）。

:::

# 1.5.2 Commutative Diagrams

%%%
number := false
tag := "kerodon-1-5-2"
%%%

Kerodon [Tag 005H](https://kerodon.net/tag/005H)

:::definition "kerodon_1_5_2_1" (lean := "SSet.Quasicategory")
Kerodon Definition 1.5.2.1（[Tag 005J](https://kerodon.net/tag/005J)）。対応表の状態：Mathlib にある。

仮定：単体集合 K と準圏 C（Kerodon と一致）。結論：K 上の図式は単体集合の射 K ⟶ C。通常の圏 D の場合は C=nerve D を取る（一致）。

:::

:::definition "kerodon_1_5_2_5" (uses := "kerodon_1_1_0_6, kerodon_1_1_6_9")
Kerodon Definition 1.5.2.5（[Tag 005N](https://kerodon.net/tag/005N)）。対応表の状態：なし。

原文は薄い非巡回の有向グラフ上の圏値図式で全ての道の合成が等しいという可換性の述語。acyclic graph/commutative graph/FreeQuiverCoverで再検索。自由quiver被覆の図式やhomotopy fiberは別の構成で、この述語ではない。

:::

:::proposition "kerodon_1_5_2_6" (uses := "kerodon_1_1_0_6, kerodon_1_5_2_5")
Kerodon Proposition 1.5.2.6（[Tag 005P](https://kerodon.net/tag/005P)）。対応表の状態：なし。

原文は指定された薄い非巡回グラフの頂点の順序・標準包含・可換図式の一意延長。acyclic graph/FreeQuiverCoverを再検索。特定scaffoldのbridgeやfree quiver coverのnerveは元の任意グラフの同じ包含ではなく、3結論の成分を直接返さない。

:::

# 1.5.3 The ∞-Category of Functors

%%%
number := false
tag := "kerodon-1-5-3"
%%%

Kerodon [Tag 005Z](https://kerodon.net/tag/005Z)

*定義 2.1 （単体的集合の積）*

単体的集合 $`X,Y` の積 $`X\times Y` を

$$`(X\times Y)([m])=X([m])\times Y([m]),\qquad (X\times Y)(\theta)=X(\theta)\times Y(\theta)`

で定める（$`\theta\colon[m]\to[m']`）。射影 $`X\times Y\to X`、$`X\times Y\to Y` は各成分への射影で与える。

*定義 2.3 （後合成）*

単体的集合 $`K` と射 $`q\colon X\to S` について、射 $`q_*\colon\mathrm{Fun}(K,X)\to\mathrm{Fun}(K,S)` を、$`n` 単体 $`f\colon K\times\Delta^n\to X` を $`q\circ f` に送ることで定める（$`\mathrm{Fun}` は定義 2.2）。

*定義 2.5 （合成と恒等射）*

単体的集合 $`X,Y,Z` について、合成 $`\circ\colon\mathrm{Fun}(Y,Z)\times\mathrm{Fun}(X,Y)\to\mathrm{Fun}(X,Z)` を、$`n` 単体 $`g\colon Y\times\Delta^n\to Z`、$`f\colon X\times\Delta^n\to Y` に対して

$$`g\circ f\colon X\times\Delta^n\xrightarrow{(f,\ \mathrm{pr}_{\Delta^n})}Y\times\Delta^n\xrightarrow{\ g\ }Z`

で定める。恒等射 $`\mathrm{id}_X` は、射影 $`X\times\Delta^0\to X` で与えられる $`\mathrm{Fun}(X,X)` の 0 単体とする。

*定理 2.6 （合成の性質）*

定義 2.5 の合成は単体的集合の射であり、結合的で、$`\mathrm{id}` を単位とする。

:::definition "kerodon_1_5_3_1" (lean := "CategoryTheory.ihom")
Kerodon Construction 1.5.3.1（[Tag 0060](https://kerodon.net/tag/0060)）。対応表の状態：Mathlib にある。

仮定：任意の単体集合 S,T（Kerodon と一致。Lean の ihom は一般のモノイダル閉圏で定義される）。結論：(ihom S).obj T は内部 Hom。次数 n の評価を Yoneda と随伴で読むと Hom(Δ\[n\] × S,T) になる。積の因子順は対称性で対応する（一致）。

*定義 2.2 （写像単体的集合 $`\mathrm{Fun}(X,Y)`）*

$`\theta\colon[m]\to[n]` について、$`\theta_*\colon\Delta^m\to\Delta^n` を $`\theta` との合成 $`\alpha\mapsto\theta\circ\alpha` で定まる単体的集合の射とする。単体的集合 $`X,Y` について、単体的集合 $`\mathrm{Fun}(X,Y)` を

$$`\mathrm{Fun}(X,Y)([n])=\mathrm{Hom}_{\mathrm{sSet}}(X\times\Delta^n,Y),\qquad \mathrm{Fun}(X,Y)(\theta)(f)=f\circ(\mathrm{id}_X\times\theta_*)`

で定める。

:::

:::proposition "kerodon_1_5_3_2" (lean := "CategoryTheory.ihom.adjunction, CategoryTheory.MonoidalClosed.curry")
Kerodon Proposition 1.5.3.2（[Tag 0061](https://kerodon.net/tag/0061)）。対応表の状態：Mathlib にある。

仮定：単体集合 S,T,U（Kerodon と一致。Lean の随伴は一般のモノイダル閉圏に適用できる）。結論：ihom.adjunction は Hom(U,ihom(S,T)) と Hom(S × U,T) の全単射。curry の逆が評価との合成で、原文の U × S には積の対称性で移る（一致）。

*定理 2.4 （積と写像単体的集合の随伴）*

単体的集合 $`X` を固定すると、単体的集合 $`Z,Y` について自然な全単射

$$`\mathrm{Hom}_{\mathrm{sSet}}(Z\times X,Y)\cong\mathrm{Hom}_{\mathrm{sSet}}(Z,\mathrm{Fun}(X,Y))`

がある。すなわち $`(-)\times X` は $`\mathrm{Fun}(X,-)` の左随伴である。

:::

:::proposition "kerodon_1_5_3_3" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.nerveFunctorCategoryIso, SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.nerveFunctorCategoryIso_uncurry")
Kerodon Proposition 1.5.3.3（[Tag 0062](https://kerodon.net/tag/0062)）。対応表の状態：本体にある。

仮定：通常の圏 C,D と評価関手（Kerodon と一致。Lean では同じ宇宙に置く）。結論：nerveFunctorCategoryIso は N(C ⥤ D) ≅ (ihom (N C)).obj (N D)。uncurry 補題は積の比較を挟むと N(評価) を与えることを確認する（一致）。

:::

:::corollary "kerodon_1_5_3_4" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.nerveFunctorCategoryIso, CategoryTheory.nerveFunctorCompHoFunctorIso")
Kerodon Corollary 1.5.3.4（[Tag 0063](https://kerodon.net/tag/0063)）。対応表の状態：本体にある。

仮定：通常の圏 C,D（Kerodon と一致）。結論：nerveFunctorCategoryIso を hoFunctor で写し、余単位の nerveFunctorCompHoFunctorIso を用いると、C ⥤ D と hFun(N C,N D) の比較同型が得られる（一致）。

:::

:::corollary "kerodon_1_5_3_5"
Kerodon Corollary 1.5.3.5（[Tag 0064](https://kerodon.net/tag/0064)）。対応表の状態：一部。

原文のρSは全次数の単体集合の同型。nerveAdjunction.homEquiv はhS→Dの関手とS→N(D)の全単射で、ρSの0単体（次数0に限定）の同じHom対応を直接与える。全次数・面退化の可換性までは含まない。

宣言：`CategoryTheory.nerveAdjunction`

:::

:::corollary "kerodon_1_5_3_6" (lean := "CategoryTheory.hoFunctor.preservesFiniteProducts, CategoryTheory.hoFunctor.isIso_prodComparison")
Kerodon Corollary 1.5.3.6（[Tag 0065](https://kerodon.net/tag/0065)）。対応表の状態：Mathlib にある。

仮定：単体集合の圏と通常圏の圏（Kerodon と一致）。結論：hoFunctor.preservesFiniteProducts が空積を含む有限積の保存、isIso\_prodComparison が二項積の比較射の同型性を与える（一致）。

:::

:::theorem "kerodon_1_5_3_7"
Kerodon Theorem 1.5.3.7（[Tag 0066](https://kerodon.net/tag/0066)）。対応表の状態：Mathlib にある。

仮定：任意の単体集合 A と準圏 X（Kerodon と一致）。結論：instQuasicategoryObjIhom は (ihom A).obj X が準圏であることを与える（一致）。

宣言：`SSet.instQuasicategoryObjIhom`

:::

:::definition "kerodon_1_5_3_8"
Kerodon Definition 1.5.3.8（[Tag 0067](https://kerodon.net/tag/0067)）。対応表の状態：Mathlib にある。

仮定：準圏 C,D（Lean が弱い：ihom の準圏性には標的 D の準圏性だけでよい）。結論：準圏 (ihom C).obj D が Fun(C,D)。instQuasicategoryObjIhom がその準圏構造を与える（一致）。

宣言：`SSet.instQuasicategoryObjIhom`

:::

# 1.5.4 Digression: Lifting Properties

%%%
number := false
tag := "kerodon-1-5-4"
%%%

Kerodon [Tag 006B](https://kerodon.net/tag/006B)

:::definition "kerodon_1_5_4_1" (lean := "CategoryTheory.CommSq, CategoryTheory.CommSq.LiftStruct")
Kerodon Definition 1.5.4.1（[Tag 006C](https://kerodon.net/tag/006C)）。対応表の状態：Mathlib にある。

仮定：圏 C と二つの射を縦辺に持つ四角形（Kerodon と一致）。結論：CommSq は四角形の可換性、LiftStruct は上下二つの三角形を可換にする対角射のデータ（一致）。

:::

:::definition "kerodon_1_5_4_3" (lean := "CategoryTheory.HasLiftingProperty, CategoryTheory.MorphismProperty.llp")
Kerodon Definition 1.5.4.3（[Tag 006E](https://kerodon.net/tag/006E)）。対応表の状態：Mathlib にある。

仮定：圏 C の二射 f,g（Kerodon と一致）。結論：HasLiftingProperty f g は f と g を縦辺に持つすべての可換正方形に持ち上げがあること。llp は g を指定クラス全体に渡らせる（一致）。

*定義 5.2 （右持ち上げ性質）*

単体的集合の射 $`q\colon E\to B` が部分単体的集合の包含 $`A\subseteq A'` に対して右持ち上げ性質をもつとは、射 $`u\colon A\to E`、$`v\colon A'\to B` が $`q\circ u=v|_A` をみたすとき、必ず射 $`w\colon A'\to E` で $`w|_A=u`、$`q\circ w=v` となるものが存在することをいう。

:::

:::definition "kerodon_1_5_4_4" (lean := "CategoryTheory.MorphismProperty.IsStableUnderCobaseChange")
Kerodon Definition 1.5.4.4（[Tag 006F](https://kerodon.net/tag/006F)）。対応表の状態：Mathlib にある。

仮定：押し出しを持つ圏 C と射クラス P（Lean が弱い：IsStableUnderCobaseChange は各押し出し正方形を条件として取る）。結論：押し出しで移された射が、元の射と同じクラス P に入ることを要求する（一致）。

:::

:::proposition "kerodon_1_5_4_5" (lean := "CategoryTheory.MorphismProperty.llp_isStableUnderCobaseChange")
Kerodon Proposition 1.5.4.5（[Tag 006G](https://kerodon.net/tag/006G)）。対応表の状態：Mathlib にある。

仮定：押し出しを持つ圏 C と射クラス T（Lean が弱い：任意の圏の押し出し正方形について述べる）。結論：llp\_isStableUnderCobaseChange は T に対する左持ち上げ性が押し出しで保たれることを与える（一致）。

:::

:::definition "kerodon_1_5_4_6" (lean := "CategoryTheory.Retract")
Kerodon Definition 1.5.4.6（[Tag 006H](https://kerodon.net/tag/006H)）。対応表の状態：Mathlib にある。

仮定：圏 C の二対象 A,B（Kerodon と一致）。結論：Retract A B は i:A⟶B と r:B⟶A、i≫r=𝟙 A を持つ（一致）。

:::

:::definition "kerodon_1_5_4_7" (lean := "CategoryTheory.RetractArrow, CategoryTheory.MorphismProperty.IsStableUnderRetracts")
Kerodon Variant 1.5.4.7（[Tag 006J](https://kerodon.net/tag/006J)）。対応表の状態：Mathlib にある。

仮定：圏 C の二射 f,f′（Kerodon と一致）。結論：RetractArrow は Arrow C におけるレトラクト、すなわち始域・終域双方の射が元の二射と可換なレトラクト。IsStableUnderRetracts はその関係での射クラスの閉性（一致）。

:::

:::proposition "kerodon_1_5_4_9" (lean := "CategoryTheory.MorphismProperty.llp_isStableUnderRetracts")
Kerodon Proposition 1.5.4.9（[Tag 006L](https://kerodon.net/tag/006L)）。対応表の状態：Mathlib にある。

仮定：圏 C と任意の射クラス T（Kerodon と一致）。結論：llp\_isStableUnderRetracts は左持ち上げ性を持つ射のレトラクトも T に対する左持ち上げ性を持つことを与える（一致）。

:::

:::definition "kerodon_1_5_4_10" (lean := "CategoryTheory.MorphismProperty.TransfiniteCompositionOfShape, CategoryTheory.MorphismProperty.transfiniteCompositions")
Kerodon Definition 1.5.4.10（[Tag 006M](https://kerodon.net/tag/006M)）。対応表の状態：Mathlib にある。

仮定：圏 C と射クラス W（Lean が弱い：順序数の閉区間のほか、整礎線形順序で底と後続を備える shape を許す）。結論：TransfiniteCompositionOfShape は初項から連続図式の余極限への射を表し、非最大の各添字の後続射に W を要求する。transfiniteCompositions は shape にわたる和（一致）。

:::

:::proposition "kerodon_1_5_4_12" (lean := "CategoryTheory.MorphismProperty.isStableUnderTransfiniteCompositionOfShape_llp")
Kerodon Proposition 1.5.4.12（[Tag 006R](https://kerodon.net/tag/006R)）。対応表の状態：Mathlib にある。

仮定：圏 C と射クラス T（Lean が弱い：順序数の区間を含む、底と後続を備えた整礎線形順序を扱う）。結論：isStableUnderTransfiniteCompositionOfShape\_llp は各後続射が T.llp の連続図式の超限合成も T.llp に入ることを与える（一致）。

:::

:::definition "kerodon_1_5_4_13" (uses := "kerodon_1_5_4_4, kerodon_1_5_4_7, kerodon_1_5_4_10")
Kerodon Definition 1.5.4.13（[Tag 006S](https://kerodon.net/tag/006S)）。対応表の状態：一部。

原文のweakly saturatedの条件は押し出し・retract・超限合成で閉じること。三つの IsStableUnder… の型はこの各条件を直接表し、弱飽和性の述語の成分に対応する。三条件をまとめた名前付きの述語や生成閉包そのものと同一視しない。

宣言：`CategoryTheory.MorphismProperty.IsStableUnderCobaseChange`、`CategoryTheory.MorphismProperty.IsStableUnderRetracts`、`CategoryTheory.MorphismProperty.IsStableUnderTransfiniteComposition`

:::

:::proposition "kerodon_1_5_4_14" (lean := "CategoryTheory.MorphismProperty.llp_isStableUnderCobaseChange, CategoryTheory.MorphismProperty.llp_isStableUnderRetracts, CategoryTheory.MorphismProperty.isStableUnderTransfiniteCompositionOfShape_llp")
Kerodon Proposition 1.5.4.14（[Tag 006T](https://kerodon.net/tag/006T)）。対応表の状態：Mathlib にある。

仮定：小余極限を持つ圏 C と射クラス T（Lean が弱い：安定性は該当する押し出し・超限合成のデータを条件として述べる）。結論：三つのインスタンスが T.llp の押し出し・レトラクト・超限合成に対する閉性を与える。弱飽和の三条件を個別に満たす（一致）。

:::

# 1.5.5 Trivial Kan Fibrations

%%%
number := false
tag := "kerodon-1-5-5"
%%%

Kerodon [Tag 006V](https://kerodon.net/tag/006V)

:::definition "kerodon_1_5_5_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibrations, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibration_iff_boundary")
Kerodon Definition 1.5.5.1（[Tag 006W](https://kerodon.net/tag/006W)）。対応表の状態：本体にある。

仮定：単体集合の射 q:X⟶Y（Kerodon と一致）。結論：trivialKanFibration\_iff\_boundary は TrivialKanFibration q と、次数 0 を含む全ての ∂Δ\[n\]⟶Δ\[n\] に対する右持ち上げ性を同値とする（一致）。

*定義 5.3 （fibration）*

- 名前　／　包含
- trivial Kan fibration　／　$`\partial\Delta^n\subseteq\Delta^n`（$`n\ge0`、定義 5.1）

:::

:::proposition "kerodon_1_5_5_4" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibration_iff_boundary, SSet.rlp_monomorphisms")
Kerodon Proposition 1.5.5.4（[Tag 006Y](https://kerodon.net/tag/006Y)）。対応表の状態：本体と Mathlib にある。

仮定：単体集合の射 p（Kerodon と一致）。結論：trivialKanFibration\_iff\_boundary と rlp\_monomorphisms により、境界包含への右持ち上げ性と任意の単射への右持ち上げ性が同値（一致）。

:::

:::corollary "kerodon_1_5_5_5" (uses := "kerodon_1_1_0_6, kerodon_1_5_5_4")
Kerodon Corollary 1.5.5.5（[Tag 006Z](https://kerodon.net/tag/006Z)）。対応表の状態：一部。

原文(a)の切断の存在はexists\_sectionの型の結論そのもの（TrivialKanFibrationの全単射RLPを適用）。(b)の指定向きのfiberwise収縮について、引用のexists\_vertical\_contractionはid→p≫sと逆端点順なので一致としない。(a)だけを数える。

宣言：`SerrePositivity.SimplicialModel.MonoRightLiftingContraction.exists_section`、`SerrePositivity.SimplicialModel.MonoRightLiftingContraction.exists_vertical_contraction`

:::

:::corollary "kerodon_1_5_5_6"
Kerodon Corollary 1.5.5.6（[Tag 0070](https://kerodon.net/tag/0070)）。対応表の状態：本体にある。

仮定：単射i:A→Bとtrivial Kan fibration p:E→Y（原文と一致）。結論：trivialKanFibration\_pullbackObjObjπ は internalHom.PullbackObjObj i p の標準比較射πがtrivial Kan fibration（原文のθと一致）。引き戻しの選択をデータとして明示し、A=空に限定しない。模型圏の追加仮定なし。

宣言：`SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.trivialKanFibration_pullbackObjObjπ`

:::

:::corollary "kerodon_1_5_5_7" (lean := "SerrePositivity.KST.SConstruction.ihomMap_trivialKanFibration")
Kerodon Corollary 1.5.5.7（[Tag 0071](https://kerodon.net/tag/0071)）。対応表の状態：本体にある。

仮定：自明 Kan fibration p:X⟶Y と任意の単体集合 B（Kerodon と一致）。結論：ihomMap\_trivialKanFibration は Fun(B,X)⟶Fun(B,Y) に TrivialKanFibration を与える（一致）。

:::

:::definition "kerodon_1_5_5_8" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan, SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.isContractibleKan_iff_trivialKanFibration")
Kerodon Definition 1.5.5.8（[Tag 0072](https://kerodon.net/tag/0072)）。対応表の状態：本体にある。

仮定：単体集合 X（Kerodon と一致）。結論：isContractibleKan\_iff\_trivialKanFibration は全境界を充填できる IsContractibleKan X と終対象 Δ\[0\] への射の自明 Kan fibration 性を同値にする（一致）。

*定義 5.4 （可縮）*

単体的集合 $`X` が可縮であるとは、$`X\to\Delta^0` が trivial Kan fibration（定義 5.3）であること、すなわち任意の射 $`\partial\Delta^n\to X`（$`n\ge0`）が $`\Delta^n\to X` に延長できることをいう。

:::

:::proposition "kerodon_1_5_5_11"
Kerodon Proposition 1.5.5.11（[Tag 050J](https://kerodon.net/tag/050J)）。対応表の状態：なし。

原文は始域XのKan・可縮Kan・準圏性を終域Yへ移す3結論。候補の二型は終域の性質を始域へ移す逆の主張で、同じpに対するいずれの結論成分も直接返さない。反対向きに使うには別の議論が必要。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.isContractibleKan_of_trivialKanFibration`、`SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.kanComplex_of_trivialKanFibration_target`

:::

:::corollary "kerodon_1_5_5_12" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.isContractibleKan_iff_trivialKanFibration, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibrations")
Kerodon Corollary 1.5.5.12（[Tag 0075](https://kerodon.net/tag/0075)）。対応表の状態：本体にある。

仮定：単体集合 X（Kerodon と一致）。結論：終対象への射に isContractibleKan\_iff\_trivialKanFibration を適用し、trivialKanFibrations の定義を展開すると、任意の単射 A⟶B に沿う A⟶X の延長の存在と同値（一致）。

:::

:::corollary "kerodon_1_5_5_13" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan.kanComplex")
Kerodon Corollary 1.5.5.13（[Tag 0076](https://kerodon.net/tag/0076)）。対応表の状態：本体にある。

仮定：IsContractibleKan X（Kerodon と一致）。結論：IsContractibleKan.kanComplex が KanComplex X を与え、その準圏性は Mathlib のインスタンスから得られる（一致）。

:::

:::proposition "kerodon_1_5_5_14" (lean := "SerrePositivity.SimplicialModel.boundaryGenerators_leftClass, SSet.rlp_monomorphisms")
Kerodon Proposition 1.5.5.14（[Tag 0077](https://kerodon.net/tag/0077)）。対応表の状態：本体と Mathlib にある。

仮定：単体集合の圏と境界包含の全クラス I（Kerodon と一致）。結論：boundaryGenerators\_leftClass は I.rlp.llp が全ての単射のクラスに等しいこと、rlp\_monomorphisms は両クラスの右直交が等しいことを与える（一致。弱飽和と境界からの生成は左持ち上げ性の閉性および相対セル分解で読む）。

:::

# 1.5.6 Uniqueness of Composition

%%%
number := false
tag := "kerodon-1-5-6"
%%%

Kerodon [Tag 0078](https://kerodon.net/tag/0078)

:::theorem "kerodon_1_5_6_1" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_1_5_4_14, kerodon_1_5_6_7, kerodon_1_5_6_9")
Kerodon Theorem 1.5.6.1（[Tag 0079](https://kerodon.net/tag/0079)）。対応表の状態：一部。

原文の(1)⇒(2)は、innerAnodyneExtensions.horn\_ι でΛ²₁の包含を指定し trivialKanFibration\_pre\_of\_innerAnodyne に適用して直接得られる。単一の制限射の自明Kan性⇒準圏性の逆向きはこの型に含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.trivialKanFibration_pre_of_innerAnodyne`、`SSet.innerAnodyneExtensions.horn_ι`

:::

:::corollary "kerodon_1_5_6_2" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.compositionTriangleSpace_isContractibleKan")
Kerodon Corollary 1.5.6.2（[Tag 007A](https://kerodon.net/tag/007A)）。対応表の状態：本体にある。

仮定：準圏 C の可合成な二辺 f,g（Kerodon と一致）。結論：compositionTriangleSpace\_isContractibleKan は内ホーン Λ\[2,1\] の指定点の上の Fun(Δ\[2\],C) の制限射のファイバーに IsContractibleKan を与える（一致）。

:::

:::definition "kerodon_1_5_6_4" (lean := "SSet.innerAnodyneExtensions, SSet.innerAnodyneExtensions_eq_retracts_transfiniteCompositions")
Kerodon Definition 1.5.6.4（[Tag 007C](https://kerodon.net/tag/007C)）。対応表の状態：Mathlib にある。

仮定：単体集合の射 f:A⟶B（Kerodon と一致）。結論：innerAnodyneExtensions のクラスは内ホーンの余積、押し出し、超限合成、レトラクトで作るクラスと等しい（一致）。

:::

:::proposition "kerodon_1_5_6_7" (lean := "SSet.quasicategory_of_innerFibration, SerrePositivity.KST.Fibration.exists_extension_of_innerAnodyne")
Kerodon Proposition 1.5.6.7（[Tag 007E](https://kerodon.net/tag/007E)）。対応表の状態：本体と Mathlib にある。

仮定：単体集合 X（Kerodon と一致）。結論：X の準圏性から exists\_extension\_of\_innerAnodyne が全 inner anodyne に沿う延長を与える。逆は内ホーンを選び、点への inner fibration の型を介して準圏性を得る（一致）。

:::

:::definition "kerodon_1_5_6_8" (uses := "kerodon_1_1_0_6, kerodon_1_3_4_1, kerodon_1_5_4_13")
Kerodon Variant 1.5.6.8（[Tag 00J2](https://kerodon.net/tag/00J2)）。対応表の状態：なし。

原文はnerveであることと全inner anodyneに沿う一意延長の iff。innerAnodyne/unique/nerveを再検索。scaffoldやsequential telescopeの特定の包含のinner anodyne性は、一意延長を全inner anodyneで結論する型ではなく、別の射の類似としてのみ記録する。

:::

:::lemma_ "kerodon_1_5_6_9" (uses := "kerodon_1_1_0_6, kerodon_1_5_5_14")
Kerodon Lemma 1.5.6.9（[Tag 007F](https://kerodon.net/tag/007F)）。対応表の状態：一部。

原文(a)の単射とΛ²₁包含のpushout-productのinner anodyne性は、innerAnodyneExtensions\_pushoutObjObjι に horn\_ι を渡した同じ比較射について直接得られる。(b)のこの生成系だけによる弱飽和生成は含めない。

宣言：`SSet.innerAnodyneExtensions_pushoutObjObjι`、`SSet.innerAnodyneExtensions.horn_ι`

:::

# 1.5.7 Universality of Path Categories

%%%
number := false
tag := "kerodon-1-5-7"
%%%

Kerodon [Tag 00J3](https://kerodon.net/tag/00J3)

:::theorem "kerodon_1_5_7_1" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_1_5_7_3, kerodon_1_5_7_6")
Kerodon Theorem 1.5.7.1（[Tag 00J4](https://kerodon.net/tag/00J4)）。対応表の状態：なし。

原文は任意のGの指定射G\_•→N(Path\[G\])による制限。候補はsequentialSpine⊂N(ℕ)という別の明示された射のinner anodyne性と一般の前合成定理。これを原文の鎖グラフの指定射と同定する比較は引用型にない。単に可算の類似としてspecialにしない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.sequentialSpine_inclusion_innerAnodyne`、`SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.trivialKanFibration_pre_of_innerAnodyne`

:::

:::proposition "kerodon_1_5_7_3" (uses := "kerodon_1_1_0_6, kerodon_1_5_6_4")
Kerodon Proposition 1.5.7.3（[Tag 00J6](https://kerodon.net/tag/00J6)）。対応表の状態：なし。

原文はグラフの標準射G\_•→N(Path\[G\])のinner anodyne性。sequentialSpineの包含は始域の部分複体と標的が別に定義された射で、同じグラフの標準射との同定が未提示。別の射についての類似の結論は§8.1ではnone。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.sequentialSpine_inclusion_innerAnodyne`

:::

:::lemma_ "kerodon_1_5_7_5"
Kerodon Lemma 1.5.7.5（[Tag 00J8](https://kerodon.net/tag/00J8)）。対応表の状態：Mathlib にある。

仮定：単体集合の単射 f,g と f の inner anodyne 性（Kerodon と一致）。結論：innerAnodyneExtensions\_pushoutObjObjι と双対順序の補題は (Y×X′) ⨿ (X×Y′) を X×X′ 上で貼った対象から Y×Y′ への pushout-product が inner anodyne であることを与える（一致）。

宣言：`SSet.innerAnodyneExtensions_pushoutObjObjι'`、`SSet.innerAnodyneExtensions_pushoutObjObjι`

:::

:::proposition "kerodon_1_5_7_6" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.trivialKanFibration_pre_of_innerAnodyne")
Kerodon Proposition 1.5.7.6（[Tag 00J9](https://kerodon.net/tag/00J9)）。対応表の状態：本体にある。

仮定：inner anodyne 射 i:A⟶B と準圏 X（Kerodon と一致。Lean は単射性を別の仮定にしない）。結論：trivialKanFibration\_pre\_of\_innerAnodyne は Fun(B,X)⟶Fun(A,X) が TrivialKanFibration であることを与える（一致）。

:::

:::corollary "kerodon_1_5_7_9"
Kerodon Corollary 1.5.7.9（[Tag 05HU](https://kerodon.net/tag/05HU)）。対応表の状態：一部。

原文の必要方向について、Nerve.strictSegal/IsStrictSegalはnerveのn単体からn本の可合成辺列（spineの射）への全単射を直接与える。Sの一般の再構成はTODOなので、spineの一意延長条件からnerveとの同型を作る逆方向は含めない。

宣言：`CategoryTheory.Nerve.strictSegal`、`CategoryTheory.Nerve.isStrictSegal`

:::

