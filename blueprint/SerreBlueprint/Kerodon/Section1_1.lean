import Verso
import VersoManual
import VersoBlueprint
import Mathlib.AlgebraicTopology.SimplexCategory.Defs
import Mathlib.AlgebraicTopology.SimplexCategory.GeneratorsRelations.Basic
import Mathlib.AlgebraicTopology.SimplexCategory.SemiSimplexCategory
import Mathlib.AlgebraicTopology.SimplicialObject.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
import Mathlib.AlgebraicTopology.SimplicialSet.CompStruct
import Mathlib.AlgebraicTopology.SimplicialSet.Degenerate
import Mathlib.AlgebraicTopology.SimplicialSet.FiniteProd
import Mathlib.AlgebraicTopology.SimplicialSet.HomotopyCat
import Mathlib.AlgebraicTopology.SimplicialSet.Skeleton
import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Functor.Const
import Mathlib.CategoryTheory.Limits.IsConnected
import Mathlib.Combinatorics.Quiver.Basic
import SerrePositivity.CategoryTheory.Simplex.GenRelEquivalence
import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.PiZeroConstant

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "1.1 Simplicial Sets" =>
%%%
number := false
tag := "kerodon-1-1"
%%%

Kerodon の 1.1 節（[Tag 0004](https://kerodon.net/tag/0004)）の項目と、SerrePositivity・Mathlib の宣言との対応。本文は対応表（research/kerodon-coverage）の判定の理由の要約で、Kerodon の本文の写しではない。

:::definition "kerodon_1_1_0_1"
Kerodon Notation 1.1.0.1（[Tag 0009](https://kerodon.net/tag/0009)）。対応表の状態：Mathlib にある。

仮定：非負整数 n（Kerodon と一致）。結論：SimplexCategory.mk n は長さ n の対象 ⦋n⦌、すなわち 0,…,n の順序集合を表す（一致）。

宣言：`SimplexCategory.mk`

:::

:::definition "kerodon_1_1_0_2" (lean := "SimplexCategory")
Kerodon Definition 1.1.0.2（[Tag 000A](https://kerodon.net/tag/000A)）。対応表の状態：Mathlib にある。

仮定：非空有限順序集合の標準形 \[n\] を使う（Kerodon と一致）。結論：SimplexCategory の対象は長さ n、\[m\] から \[n\] の射は Fin (m+1) →o Fin (n+1) の順序写像（一致）。

:::

:::definition "kerodon_1_1_0_4" (lean := "CategoryTheory.SimplicialObject, CategoryTheory.CosimplicialObject")
Kerodon Definition 1.1.0.4（[Tag 000C](https://kerodon.net/tag/000C)）。対応表の状態：Mathlib にある。

仮定：任意の圏 C（Kerodon と一致）。結論：SimplicialObject C は Δᵒᵖ ⥤ C、CosimplicialObject C は Δ ⥤ C（一致）。

:::

:::definition "kerodon_1_1_0_5" (lean := "CategoryTheory.SimplicialObject")
Kerodon Notation 1.1.0.5（[Tag 000D](https://kerodon.net/tag/000D)）。対応表の状態：Mathlib にある。

仮定：圏 C、単体対象または余単体対象、次数 n（Kerodon と一致）。結論：関手の obj を反対圏の \[n\] または \[n\] に適用した値が Cₙ または Cⁿ。引用は単体対象の型で、次数別の記法は関手評価で読む（一致）。

:::

:::definition "kerodon_1_1_0_6" (lean := "SSet")
Kerodon Definition 1.1.0.6（[Tag 000H](https://kerodon.net/tag/000H)）。対応表の状態：Mathlib にある。

仮定：値を集合の圏に取る（Kerodon と一致。Lean の集合は Type u）。結論：SSet は Δᵒᵖ から Type u への関手の型（一致）。

:::

:::definition "kerodon_1_1_0_7" (lean := "SSet")
Kerodon Notation 1.1.0.7（[Tag 04Z5](https://kerodon.net/tag/04Z5)）。対応表の状態：Mathlib にある。

仮定：単体圏の反対圏を始域、集合の圏を終域とする（Kerodon と一致）。結論：SSet に関手圏の圏構造が入り、射は単体集合間の自然変換（一致）。

:::

:::definition "kerodon_1_1_0_11" (lean := "SSet")
Kerodon Definition 1.1.0.11（[Tag 04Z7](https://kerodon.net/tag/04Z7)）。対応表の状態：Mathlib にある。

仮定：単体集合 X、非負次数 n（Kerodon と一致）。結論：X.obj (op ⦋n⦌) の元が n 単体。n=0 と n=1 が頂点と辺（一致）。

:::

:::proposition "kerodon_1_1_0_12" (lean := "SSet.yonedaEquiv")
Kerodon Proposition 1.1.0.12（[Tag 04Z8](https://kerodon.net/tag/04Z8)）。対応表の状態：Mathlib にある。

仮定：単体集合 X と標準単体の次数 n（Kerodon と一致）。結論：SSet.yonedaEquiv は Δ\[n\] ⟶ X と X の n 単体との全単射で、恒等単体での評価を使う（一致）。

:::

:::definition "kerodon_1_1_0_13" (lean := "SSet.yonedaEquiv")
Kerodon Notation 1.1.0.13（[Tag 04Z9](https://kerodon.net/tag/04Z9)）。対応表の状態：Mathlib にある。

仮定：X の n 単体 x（Kerodon と一致）。結論：SSet.yonedaEquiv.symm x は x を表す Δ\[n\] ⟶ X で、恒等単体への適用で x を返す（一致）。

:::

# 1.1.1 Face Operators

%%%
number := false
tag := "kerodon-1-1-1"
%%%

Kerodon [Tag 04ZB](https://kerodon.net/tag/04ZB)

:::definition "kerodon_1_1_1_1" (lean := "SemiSimplexCategory")
Kerodon Notation 1.1.1.1（[Tag 04ZC](https://kerodon.net/tag/04ZC)）。対応表の状態：Mathlib にある。

仮定：対象を非空有限順序集合の標準形 \[n\] に取る（Kerodon と一致）。結論：SemiSimplexCategory の射は有限順序集合の順序埋め込み、すなわち狭義単調写像（一致）。

:::

:::definition "kerodon_1_1_1_2"
Kerodon Definition 1.1.1.2（[Tag 04ZD](https://kerodon.net/tag/04ZD)）。対応表の状態：一部。

半単体圏はあるが、そこからの反変関手を名付けた半単体対象の定義は引用先にない。

宣言：`SemiSimplexCategory`

:::

:::definition "kerodon_1_1_1_4"
Kerodon Construction 1.1.1.4（[Tag 04ZE](https://kerodon.net/tag/04ZE)）。対応表の状態：一部。

単体対象の面作用素はある。引用先には半単体対象の面作用素の構成がない。名前空間もCategoryTheory.SimplicialObjectへ補正する。

宣言：`SimplexCategory.δ`、`CategoryTheory.SimplicialObject.δ`

:::

:::proposition "kerodon_1_1_1_9"
Kerodon Proposition 1.1.1.9（[Tag 04FQ](https://kerodon.net/tag/04FQ)）。対応表の状態：なし。

確認済み・なし（対象ソースの探索範囲内）。半単体対象・面作用素の表示を検索。SemiSimplexCategoryの定義とΔ全体の表示はあるが、面だけの関係式からの半単体対象構成は見つからない。

:::

# 1.1.2 Degeneracy Operators

%%%
number := false
tag := "kerodon-1-1-2"
%%%

Kerodon [Tag 04ZJ](https://kerodon.net/tag/04ZJ)

:::definition "kerodon_1_1_2_1"
Kerodon Construction 1.1.2.1（[Tag 04ZK](https://kerodon.net/tag/04ZK)）。対応表の状態：Mathlib にある。

仮定：非負整数 n、i : Fin (n+1)、圏 C の単体対象（Kerodon と一致）。結論：SimplexCategory.σ は \[n+1\] → \[n\] で i と i+1 を同一視し、SimplicialObject.σ は反変評価 Cₙ ⟶ Cₙ₊₁（一致）。

宣言：`SimplexCategory.σ`、`CategoryTheory.SimplicialObject.σ`

:::

:::definition "kerodon_1_1_2_2" (lean := "SSet.Edge.id")
Kerodon Notation 1.1.2.2（[Tag 04ZL](https://kerodon.net/tag/04ZL)）。対応表の状態：Mathlib にある。

仮定：単体集合 X と頂点 x（Kerodon と一致）。結論：Edge.id x は 0 番の退化で得る始点も終点も x の辺（一致）。

:::

:::definition "kerodon_1_1_2_3" (lean := "SSet.degenerate, SSet.nonDegenerate, SSet.degenerate_zero")
Kerodon Definition 1.1.2.3（[Tag 0012](https://kerodon.net/tag/0012)）。対応表の状態：Mathlib にある。

仮定：単体集合 X と非負次数 n（Kerodon と一致）。結論：degenerate は低次への全射に沿う像の和で、degenerate\_eq\_iUnion\_range\_σ が個々の退化作用素の像での原文の定義と照合する。nonDegenerate は補集合、degenerate\_zero は空集合（一致）。

:::

:::proposition "kerodon_1_1_2_10"
Kerodon Proposition 1.1.2.10（[Tag 0011](https://kerodon.net/tag/0011)）。対応表の状態：一部。

原文は5条件。退化作用素の像・低次元への全射・低次元への任意射の対応は確認。任意次元への非単射写像による因子化まで含む全5条件の同値は未確認。

宣言：`SSet.mem_degenerate_iff`、`SSet.degenerate_eq_iUnion_range_σ`

:::

:::definition "kerodon_1_1_2_12"
Kerodon Notation 1.1.2.12（[Tag 04ZR](https://kerodon.net/tag/04ZR)）。対応表の状態：なし。

確認済み・なし（対象ソースの探索範囲内）。全射単体圏の名称・順序写像の全射部分圏を検索。全射の補題は多数あるが、Δ\_surjそのものの対応宣言は見つからない。

:::

:::proposition "kerodon_1_1_2_13"
Kerodon Proposition 1.1.2.13（[Tag 04FT](https://kerodon.net/tag/04FT)）。対応表の状態：なし。

確認済み・なし（対象ソースの探索範囲内）。退化作用素のみの表示を検索。生成元・関係式によるΔ全体の圏はあるが、Δ\_surjの表示と関手の存在一意性は見つからない。

:::

:::proposition "kerodon_1_1_2_14" (lean := "SerrePositivity.SimplexPresentation.equivalence, SimplexCategoryGenRel")
Kerodon Proposition 1.1.2.14（[Tag 04FW](https://kerodon.net/tag/04FW)）。対応表の状態：本体にある。

仮定：圏 C の対象列と面・退化の作用が単体恒等式を満たす（Kerodon と一致。Lean では生成元の関係として表す）。結論：SimplexCategoryGenRel と SimplexCategory の圏同値により、反変関手の指定を生成元上の指定に移せる（一致。引用の型は圏同値で、C 値の述語を直接返す形ではない）。

:::

# 1.1.3 Dimensions of Simplicial Sets

%%%
number := false
tag := "kerodon-1-1-3"
%%%

Kerodon [Tag 04ZS](https://kerodon.net/tag/04ZS)

:::definition "kerodon_1_1_3_1"
Kerodon Definition 1.1.3.1（[Tag 0019](https://kerodon.net/tag/0019)）。対応表の状態：一部。

HasDimensionLT/LEは次元の上界。原文に含まれる次元ちょうどk・有限次元の述語までは引用されていない。負の上界はLT 0に対応。

宣言：`SSet.HasDimensionLT`、`SSet.HasDimensionLE`

:::

:::proposition "kerodon_1_1_3_6" (lean := "SSet.hasDimensionLE_prod, SSet.hasDimensionLT_prod")
Kerodon Proposition 1.1.3.6（[Tag 012R](https://kerodon.net/tag/012R)）。対応表の状態：Mathlib にある。

仮定：単体集合 X,Y に次元上界 d₁,d₂（Kerodon と一致）。結論：hasDimensionLE\_prod は X × Y の次元上界 d₁+d₂ を与える（一致）。

:::

:::proposition "kerodon_1_1_3_8" (lean := "SSet.exists_nonDegenerate, SSet.unique_nonDegenerate_map, SSet.unique_nonDegenerate_simplex, SSet.unique_nonDegenerate_dim")
Kerodon Proposition 1.1.3.8（[Tag 0014](https://kerodon.net/tag/0014)）。対応表の状態：Mathlib にある。

仮定：単体集合 X と標準 n 単体からの射、すなわち X の n 単体 x（Kerodon と一致）。結論：exists\_nonDegenerate は低次の非退化単体と全射による分解を与え、unique\_nonDegenerate\_dim・simplex・map はそれぞれ次数、単体、全射の一意性を与える（一致）。

:::

:::definition "kerodon_1_1_3_9" (lean := "CategoryTheory.Functor.Elements")
Kerodon Construction 1.1.3.9（[Tag 00X4](https://kerodon.net/tag/00X4)）。対応表の状態：Mathlib にある。

仮定：単体集合 X（Kerodon と一致）。結論：各対象 (\[n\],x) と x=X(α)(y) を満たす α:\[n\]→\[m\] の射の圏は X.Elements の反対圏に対応する（一致。Elements 自体では射の向きが逆）。

:::

:::proposition "kerodon_1_1_3_11"
Kerodon Proposition 1.1.3.11（[Tag 04ZX](https://kerodon.net/tag/04ZX)）。対応表の状態：一部。

次元上界の全射像と部分複体の和での保存。標準単体を用いる全4条件の同値までは引用されていない。

宣言：`SSet.hasDimensionLT_iSup_iff`、`SSet.hasDimensionLT_of_epi`

:::

:::corollary "kerodon_1_1_3_14"
Kerodon Corollary 1.1.3.14（[Tag 04ZZ](https://kerodon.net/tag/04ZZ)）。対応表の状態：なし。

確認済み・なし（対象ソースの探索範囲内）。Dimensionと次数切断・全単射・同型を検索。次元上界の保存補題はあるが、低次数の全単射から全体の同型を得る定理は見つからない。

:::

# 1.1.4 The Skeletal Filtration

%%%
number := false
tag := "kerodon-1-1-4"
%%%

Kerodon [Tag 0010](https://kerodon.net/tag/0010)

:::definition "kerodon_1_1_4_1" (lean := "SSet.skeleton, SSet.sk")
Kerodon Construction 1.1.4.1（[Tag 0015](https://kerodon.net/tag/0015)）。対応表の状態：Mathlib にある。

仮定：単体集合 X と整数 k（Kerodon と一致。Lean は自然数の添字を取り、k≥0 なら k+1、k\<0 なら 0 を使う）。結論：部分複体 skeleton は次数 k 以下で生成した部分複体で、負の k では skeleton 0 が空になる（一致。別の関手 sk との比較同型は引用の型には含まれない）。

:::

:::proposition "kerodon_1_1_4_6"
Kerodon Proposition 1.1.4.6（[Tag 001A](https://kerodon.net/tag/001A)）。対応表の状態：一部。

非退化単体の所属次元と低次元での全体との一致は確認。原文の次元上界とHom全単射そのものの型ではない。

宣言：`SSet.mem_skeleton_obj_iff_of_nonDegenerate`、`SSet.skeleton_obj_eq_top`

:::

:::corollary "kerodon_1_1_4_7"
Kerodon Corollary 1.1.4.7（[Tag 0501](https://kerodon.net/tag/0501)）。対応表の状態：一部。

非退化単体による包含の判定と生成単体のskeletonへの包含。最大の次元上界部分複体という一括の主張は引用されていない。

宣言：`SSet.Subcomplex.le_iff_contains_nonDegenerate`、`SSet.ofSimplex_le_skeleton`

:::

:::corollary "kerodon_1_1_4_8"
Kerodon Corollary 1.1.4.8（[Tag 0502](https://kerodon.net/tag/0502)）。対応表の状態：一部。

isColimitCoconeNはX全体の非退化単体表示。次数制限した単体圏から骨格への余極限の型ではない。

宣言：`SSet.isColimitCoconeN`

:::

:::corollary "kerodon_1_1_4_9"
Kerodon Corollary 1.1.4.9（[Tag 0503](https://kerodon.net/tag/0503)）。対応表の状態：一部。

skAdjは切断からの左随伴。原文の部分複体skeletonとの比較同型がTODOなので、その版の余極限保存は未対応。

宣言：`SSet.sk`、`SSet.skAdj`

:::

:::definition "kerodon_1_1_4_10" (lean := "SSet.boundary, SSet.boundary_obj_eq_univ")
Kerodon Construction 1.1.4.10（[Tag 000R](https://kerodon.net/tag/000R)）。対応表の状態：Mathlib にある。

仮定：非負整数 n（Kerodon と一致）。結論：boundary n は Δ\[n\] の真の面を合わせた部分複体で、次数 m\<n では boundary\_obj\_eq\_univ により全単体を含む（一致）。

:::

:::proposition "kerodon_1_1_4_12" (lean := "SSet.relativeCellComplexOfMono.isPushout, SSet.relativeCellComplexOfMono")
Kerodon Proposition 1.1.4.12（[Tag 001B](https://kerodon.net/tag/001B)）。対応表の状態：Mathlib にある。

仮定：単体集合 X と段数 k（Kerodon と一致。Lean の相対版は初期対象から X への単射に特殊化）。結論：isPushout は相対骨格の連続する段で、新しい非退化 k 単体の境界の余積に沿う押し出しを与える（一致）。

:::

:::proposition "kerodon_1_1_4_13"
Kerodon Proposition 1.1.4.13（[Tag 0504](https://kerodon.net/tag/0504)）。対応表の状態：一部。

Mathlibのhom\_extは単射性、自前のboundaryFaceGluingは次元n+2の全射性。原文が含む1次元の貼合せまで引用先だけで網羅するか未確認。引用の名前空間も補正が必要。

宣言：`SSet.boundary.hom_ext`、`SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.boundaryFaceGluing`、`SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.BoundaryFaceCompatible`

:::

# 1.1.5 Discrete Simplicial Sets

%%%
number := false
tag := "kerodon-1-1-5"
%%%

Kerodon [Tag 00FQ](https://kerodon.net/tag/00FQ)

:::proposition "kerodon_1_1_5_1"
Kerodon Proposition 1.1.5.1（[Tag 00FR](https://kerodon.net/tag/00FR)）。対応表の状態：なし。

確認済み・なし（対象ソースの探索範囲内）。次元0・定数対象・離散性と圏同値を検索。定数対象の構成とHom全単射はあるが、次元0の充満部分圏とTypeの同値は見つからない。

:::

:::definition "kerodon_1_1_5_2" (lean := "CategoryTheory.Functor.const, SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.discrete")
Kerodon Construction 1.1.5.2（[Tag 00FS](https://kerodon.net/tag/00FS)）。対応表の状態：本体と Mathlib にある。

仮定：圏 C の対象 c（Kerodon と一致）。結論：Functor.const Δᵒᵖ は全次数の値が c で作用が恒等射の単体対象。discrete は C=Type での同じ構成（一致）。

:::

:::proposition "kerodon_1_1_5_5"
Kerodon Proposition 1.1.5.5（[Tag 00FV](https://kerodon.net/tag/00FV)）。対応表の状態：一部。

一般の評価の左随伴はあるが、引用する宣言はCのHom添字の余積を仮定する。原文の任意圏の定数対象からのHom全単射そのものではない。

宣言：`CategoryTheory.evaluationAdjunctionRight`

:::

:::corollary "kerodon_1_1_5_8"
Kerodon Corollary 1.1.5.8（[Tag 00FX](https://kerodon.net/tag/00FX)）。対応表の状態：一部。

評価の一般随伴と定数-極限の随伴は材料。任意圏でconst⊣ev₀を指定した宣言としては引用されていない。

宣言：`CategoryTheory.evaluationAdjunctionRight`、`CategoryTheory.Limits.constLimAdj`

:::

:::corollary "kerodon_1_1_5_9" (lean := "CategoryTheory.isConnected_of_isInitial")
Kerodon Corollary 1.1.5.9（[Tag 00FY](https://kerodon.net/tag/00FY)）。対応表の状態：Mathlib にある。

仮定：任意の圏 C（Kerodon と一致。Lean が使う IsConnected Δᵒᵖ は \[0\] が初期対象なので満たされる）。結論：Functor.const Δᵒᵖ の充満性と忠実性により定数単体対象への埋め込みを得る（一致）。

:::

:::definition "kerodon_1_1_5_10"
Kerodon Definition 1.1.5.10（[Tag 00FZ](https://kerodon.net/tag/00FZ)）。対応表の状態：一部。

discreteは定数単体集合の構成で、定数対象と同型であるという述語ではない。自前宣言の名前空間を補う。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.discrete`

:::

:::corollary "kerodon_1_1_5_11"
Kerodon Corollary 1.1.5.11（[Tag 00G0](https://kerodon.net/tag/00G0)）。対応表の状態：一部。

定数関手のFull/Faithfulは確認したが、離散対象という本質的像の述語は引用されていない。匿名記載を実名に補正。

宣言：`CategoryTheory.instFullFunctorConstOfIsConnected`

:::

:::definition "kerodon_1_1_5_12" (lean := "CategoryTheory.Functor.const, SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.discrete")
Kerodon Notation 1.1.5.12（[Tag 00G1](https://kerodon.net/tag/00G1)）。対応表の状態：本体と Mathlib にある。

仮定：集合 T（Kerodon と一致）。結論：discrete T と Type 値の Functor.const は全次数で T を値とし、面・退化が恒等写像の単体集合（一致）。

:::

:::proposition "kerodon_1_1_5_14"
Kerodon Proposition 1.1.5.14（[Tag 00G3](https://kerodon.net/tag/00G3)）。対応表の状態：なし。

確認済み・なし（対象ソースの探索範囲内）。離散性・定数対象・作用素の全単射・次元条件を検索。特定の離散基底上の比較は別の主張で、原文の4条件の同値は見つからない。

:::

# 1.1.6 Directed Graphs as Simplicial Sets

%%%
number := false
tag := "kerodon-1-1-6"
%%%

Kerodon [Tag 001D](https://kerodon.net/tag/001D)

:::definition "kerodon_1_1_6_1" (lean := "Quiver")
Kerodon Definition 1.1.6.1（[Tag 001E](https://kerodon.net/tag/001E)）。対応表の状態：Mathlib にある。

仮定：頂点の集合と始点・終点を持つ辺（Kerodon と一致。Lean では辺を頂点対で添字付けする）。結論：Quiver V は各頂点対に辺の型を割り当て、多重辺とループを許す（一致）。

:::

:::definition "kerodon_1_1_6_5"
Kerodon Definition 1.1.6.5（[Tag 001J](https://kerodon.net/tag/001J)）。対応表の状態：一部。

Prefunctorは辺を辺に写す。原文が許す頂点への潰しを扱うには反射的quiverの射が必要で、原文のGraphそのものの定義ではない。 宣言名・出典表記も検査済みの形に補正。

宣言：`Prefunctor`、`CategoryTheory.ReflQuiver`

:::

:::proposition "kerodon_1_1_6_7" (lean := "SSet.OneTruncation₂, SSet.OneTruncation₂.map")
Kerodon Proposition 1.1.6.7（[Tag 001L](https://kerodon.net/tag/001L)）。対応表の状態：Mathlib にある。

仮定：単体集合 X,Y と単体写像 f（Kerodon と一致）。結論：OneTruncation₂.map f は頂点と辺を次数別に写し、反射的 quiver の指定自己辺である頂点の退化を保存する。非退化辺の像が退化したときは原文のグラフで頂点に写る場合に当たる（一致）。

:::

:::proposition "kerodon_1_1_6_8"
Kerodon Proposition 1.1.6.8（[Tag 001M](https://kerodon.net/tag/001M)）。対応表の状態：なし。

確認済み・なし（対象ソースの探索範囲内）。1切断quiver・グラフとHom全単射を検索。OneTruncation₂の射の構成はあるが、次元1の単体集合からのHomの全単射は見つからない。

:::

:::proposition "kerodon_1_1_6_9"
Kerodon Proposition 1.1.6.9（[Tag 001N](https://kerodon.net/tag/001N)）。対応表の状態：なし。

確認済み・なし（対象ソースの探索範囲内）。グラフと1次元単体集合の圏同値を検索。nerveの基礎quiverの同値は個々の圏への比較で、原文の圏同値ではない。

:::

