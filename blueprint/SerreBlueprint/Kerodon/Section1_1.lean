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

*規約 （大きさ）*

第 III 部を通して、Grothendieck 宇宙 $`\mathbb U` を一つ固定する。$`\mathbb U` の元である集合を小さいという。単体的集合 $`X` が小さいとは、すべての $`[m]` について $`X([m])` が小さいことをいう。

:::definition "kerodon_1_1_0_1"
Kerodon Notation 1.1.0.1（[Tag 0009](https://kerodon.net/tag/0009)）。対応表の状態：Mathlib にある。

仮定：非負整数 n（Kerodon と一致）。結論：SimplexCategory.mk n は長さ n の対象 ⦋n⦌、すなわち 0,…,n の順序集合を表す（一致）。

宣言：`SimplexCategory.mk`

:::

:::definition "kerodon_1_1_0_2" (lean := "SimplexCategory")
Kerodon Definition 1.1.0.2（[Tag 000A](https://kerodon.net/tag/000A)）。対応表の状態：Mathlib にある。

仮定：非空有限順序集合の標準形 \[n\] を使う（Kerodon と一致）。結論：SimplexCategory の対象は長さ n、\[m\] から \[n\] の射は Fin (m+1) →o Fin (n+1) の順序写像（一致）。

*定義 1.1 （単体圏 $`\Delta`）*

$`n\ge0` について、$`[n]=\{0,1,\dots,n\}` に通常の大小関係 $`0<1<\cdots<n` で全順序を入れたものを考える。単体圏 $`\Delta` を次で定める。

- 対象：$`[n]`（$`n\ge0`）。

- 射：$`\mathrm{Hom}_\Delta([m],[n])` は、順序を保つ写像 $`\theta\colon[m]\to[n]`、つまり $`i\le j` なら $`\theta(i)\le\theta(j)` をみたす写像の全体。

- 合成：写像の合成。恒等射：恒等写像。

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

*定義 1.2 （単体的集合）*

単体的集合とは関手 $`X\colon\Delta^{\mathrm{op}}\to\mathrm{Set}` のことである。単体的集合の射は関手の間の自然変換とする。

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
Kerodon Definition 1.1.1.2（[Tag 04ZD](https://kerodon.net/tag/04ZD)）。対応表の状態：なし。

原文は任意圏 C の半単体対象 SemiSimplexCategoryᵒᵖ⥤C を定義する。候補の型は半単体圏そのものの構造だけで、対象関手の定義・成分を直接与えない。圏の材料だけを partial に数えない。

宣言：`SemiSimplexCategory`

:::

:::definition "kerodon_1_1_1_4"
Kerodon Construction 1.1.1.4（[Tag 04ZE](https://kerodon.net/tag/04ZE)）。対応表の状態：一部。

原文は δ と (semi)simplicial object の面作用素を構成する。SimplexCategory.δ は Fin.succAboveOrderEmb による同じ δ、SimplicialObject.δ は X.map δ.op そのものなので、単体対象側の構成を直接与える。半単体対象側は含まない。

宣言：`SimplexCategory.δ`、`CategoryTheory.SimplicialObject.δ`

:::

:::proposition "kerodon_1_1_1_9"
Kerodon Proposition 1.1.1.9（[Tag 04FQ](https://kerodon.net/tag/04FQ)）。対応表の状態：なし。

原文は面の関係式だけから半単体対象を一意に再構成する iff。現本体全体とMathlibを semi(s)implicial・SemiSimplex・nonunital bar で再検索。半単体圏と全Δの生成関係表示はあるが、面だけの関係式を入力に取る同じ関手の再構成宣言は見つからない。

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

:::proposition "kerodon_1_1_2_10" (uses := "kerodon_1_1_0_6, kerodon_1_1_2_1")
Kerodon Proposition 1.1.2.10（[Tag 0011](https://kerodon.net/tag/0011)）。対応表の状態：一部。

原文の5条件中、degenerate\_eq\_iUnion\_range\_σ は退化作用素の像の和、mem\_degenerate\_iff は低次元への全射に沿う像との同値で、(1)と(3)の同値を定義の展開で直接与える。(5)の任意次元の非単射による因子化まで含めない。

宣言：`SSet.mem_degenerate_iff`、`SSet.degenerate_eq_iUnion_range_σ`

:::

:::definition "kerodon_1_1_2_12"
Kerodon Notation 1.1.2.12（[Tag 04ZR](https://kerodon.net/tag/04ZR)）。対応表の状態：なし。

原文は全射順序写像だけの圏Δsurjの記法・構成。Simplex/Surj・DeltaSurj・surjCategoryを現本体とMathlibで再検索。epi\_iff\_surjective等は個々のΔの射の判定で、全射のみを射とするこの圏の定義ではない。

:::

:::proposition "kerodon_1_1_2_13"
Kerodon Proposition 1.1.2.13（[Tag 04FT](https://kerodon.net/tag/04FT)）。対応表の状態：なし。

原文は退化作用素の関係式からΔsurjᵒᵖ上の関手を一意に再構成する iff。退化作用素・全射単体圏・presentationを再検索。Δ全体の面と退化の生成関係や全射の補題から、同じΔsurj上の関手を作る追加の構成が要る。

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

:::definition "kerodon_1_1_3_1" (uses := "kerodon_1_1_0_6")
Kerodon Definition 1.1.3.1（[Tag 0019](https://kerodon.net/tag/0019)）。対応表の状態：一部。

原文は次元≤k・次元ちょうどk・有限次元を定義する。HasDimensionLT/LE の型は各上位次数の全単体の退化性で、非負kの上界および負kの空の場合を直接表す。次元ちょうど・有限次元の述語はこの引用にはない。

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

:::proposition "kerodon_1_1_3_11" (uses := "kerodon_1_1_0_6, kerodon_1_1_3_8")
Kerodon Proposition 1.1.3.11（[Tag 04ZX](https://kerodon.net/tag/04ZX)）。対応表の状態：なし。

原文は次元上界と任意図式/標準単体からの余極限表示の4条件の同値。hasDimensionLT\_iSup\_iff は部分複体の和、hasDimensionLT\_of\_epi は全射像の上界であり、原文の余極限図式・標準比較写像のどれも型にない。余極限と和/全射を結ぶ別の議論が要るため部品としてのみ記録。

宣言：`SSet.hasDimensionLT_iSup_iff`、`SSet.hasDimensionLT_of_epi`

:::

:::corollary "kerodon_1_1_3_14" (uses := "kerodon_1_1_0_6")
Kerodon Corollary 1.1.3.14（[Tag 04ZZ](https://kerodon.net/tag/04ZZ)）。対応表の状態：なし。

原文は次元≤kの二対象間の同じ射fを低次数の全単射から同型とする。現本体とMathlibのDimension・truncation・isIsoを再検索。hasDimensionLT\_iff\_of\_isoは逆向きの不変性、SkeletalDimension.stageIsoは骨格包含の別の射の同型。任意fの判定には当たらない。

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

:::proposition "kerodon_1_1_4_6" (uses := "kerodon_1_1_0_6, kerodon_1_1_3_8")
Kerodon Proposition 1.1.4.6（[Tag 001A](https://kerodon.net/tag/001A)）。対応表の状態：なし。

原文は skeleton の次元上界と、低次元 T からの包含による Hom 全単射。候補は S の非退化単体の所属と低次数の成分一致で、skeleton 自身の次元上界やこの Hom 写像の全単射を直接結論しない。非退化単体分解から組み立てる追加議論は partial に数えない。

宣言：`SSet.mem_skeleton_obj_iff_of_nonDegenerate`、`SSet.skeleton_obj_eq_top`

:::

:::corollary "kerodon_1_1_4_7"
Kerodon Corollary 1.1.4.7（[Tag 0501](https://kerodon.net/tag/0501)）。対応表の状態：なし。

原文は skeleton が次元≤k の最大の部分複体。候補は一般の部分複体包含の判定と個々の低次元単体の生成部分複体の包含で、任意の次元≤kの部分複体を包含する結論ではない。最大性と次元上界を導く補助の段階に留まる。

宣言：`SSet.Subcomplex.le_iff_contains_nonDegenerate`、`SSet.ofSimplex_le_skeleton`

:::

:::corollary "kerodon_1_1_4_8"
Kerodon Corollary 1.1.4.8（[Tag 0502](https://kerodon.net/tag/0502)）。対応表の状態：なし。

原文は全ての次数≤k の単体圏による標準余極限の単射性と像の skeleton との一致。isColimitCoconeN は全次数の非退化単体の別の添字圏から X 全体への余極限であり、有限次数制限した同じ射の結論ではない。

宣言：`SSet.isColimitCoconeN`

:::

:::corollary "kerodon_1_1_4_9" (uses := "kerodon_1_1_0_6, kerodon_1_1_3_11, kerodon_1_1_3_14, kerodon_1_1_4_6")
Kerodon Corollary 1.1.4.9（[Tag 0503](https://kerodon.net/tag/0503)）。対応表の状態：なし。

原文は部分複体の k-skeleton 関手の小余極限保存。skAdj は切断から Truncated.sk への随伴で、SSet.sk と部分複体 skeleton の比較は同ファイルの TODO。異なる関手の随伴と保存から元の主張へは比較の証明が要る。

宣言：`SSet.sk`、`SSet.skAdj`

:::

:::definition "kerodon_1_1_4_10" (lean := "SSet.boundary, SSet.boundary_obj_eq_univ")
Kerodon Construction 1.1.4.10（[Tag 000R](https://kerodon.net/tag/000R)）。対応表の状態：Mathlib にある。

仮定：非負整数 n（Kerodon と一致）。結論：boundary n は Δ\[n\] の真の面を合わせた部分複体で、次数 m\<n では boundary\_obj\_eq\_univ により全単体を含む（一致）。

*定義 5.1 （境界 $`\partial\Delta^n`）*

$`n\ge0` について、$`\Delta^n` の部分単体的集合 $`\partial\Delta^n=\bigcup_{0\le j\le n}\partial_j\Delta^n` を境界という（面は定義 1.6、和は定義 1.5）。$`\partial\Delta^0` は空である。

:::

:::proposition "kerodon_1_1_4_12" (lean := "SSet.relativeCellComplexOfMono.isPushout, SSet.relativeCellComplexOfMono")
Kerodon Proposition 1.1.4.12（[Tag 001B](https://kerodon.net/tag/001B)）。対応表の状態：Mathlib にある。

仮定：単体集合 X と段数 k（Kerodon と一致。Lean の相対版は初期対象から X への単射に特殊化）。結論：isPushout は相対骨格の連続する段で、新しい非退化 k 単体の境界の余積に沿う押し出しを与える（一致）。

:::

:::proposition "kerodon_1_1_4_13" (uses := "kerodon_1_1_0_6")
Kerodon Proposition 1.1.4.13（[Tag 0504](https://kerodon.net/tag/0504)）。対応表の状態：一部。

原文の境界からの面制限写像の単射性は boundary.hom\_ext の型そのもの（n+1≥1）で直接得られる。image の整合条件について boundaryFaceGluing は境界次数n+2の構成を与えるが、全正次数を覆うとはしない。単射性という結論成分に限定する。

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

原文は次元0の充満部分圏からSetへのev₀の圏同値。dimension zero・discrete・HasDimensionLE 0で再検索。定数単体集合やΔ0の次元0のinstance、Hom対応はあるが、この充満部分圏とev₀の同値ではない。別のモデルの自由構成を同値の成分とは数えない。

:::

:::definition "kerodon_1_1_5_2" (lean := "CategoryTheory.Functor.const, SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.discrete")
Kerodon Construction 1.1.5.2（[Tag 00FS](https://kerodon.net/tag/00FS)）。対応表の状態：本体と Mathlib にある。

仮定：圏 C の対象 c（Kerodon と一致）。結論：Functor.const Δᵒᵖ は全次数の値が c で作用が恒等射の単体対象。discrete は C=Type での同じ構成（一致）。

:::

:::proposition "kerodon_1_1_5_5"
Kerodon Proposition 1.1.5.5（[Tag 00FV](https://kerodon.net/tag/00FV)）。対応表の状態：なし。

原文は任意圏の定数単体対象から X への自然変換を0成分で評価する指定写像の全単射。evaluationAdjunctionRight の左辺は Hom 添字の余積で作った evaluationLeftAdjoint で、定数対象ではない。初期対象0での比較同型と評価との整合を別に示す必要がある。

宣言：`CategoryTheory.evaluationAdjunctionRight`

:::

:::corollary "kerodon_1_1_5_8"
Kerodon Corollary 1.1.5.8（[Tag 00FX](https://kerodon.net/tag/00FX)）。対応表の状態：なし。

原文の指定随伴は const⊣ev₀。evaluationAdjunctionRight は余積から作る別の左随伴、constLimAdj は const⊣lim で、いずれも同じ左右関手の随伴ではない。ev₀とlim、または左随伴とconstを同定する追加議論を数えない。

宣言：`CategoryTheory.evaluationAdjunctionRight`、`CategoryTheory.Limits.constLimAdj`

:::

:::corollary "kerodon_1_1_5_9" (lean := "CategoryTheory.isConnected_of_isInitial")
Kerodon Corollary 1.1.5.9（[Tag 00FY](https://kerodon.net/tag/00FY)）。対応表の状態：Mathlib にある。

仮定：任意の圏 C（Kerodon と一致。Lean が使う IsConnected Δᵒᵖ は \[0\] が初期対象なので満たされる）。結論：Functor.const Δᵒᵖ の充満性と忠実性により定数単体対象への埋め込みを得る（一致）。

:::

:::definition "kerodon_1_1_5_10" (uses := "kerodon_1_1_0_6, kerodon_1_1_5_2")
Kerodon Definition 1.1.5.10（[Tag 00FZ](https://kerodon.net/tag/00FZ)）。対応表の状態：なし。

原文は X がある定数単体集合と同型であるという離散性の述語。discrete:T↦const T は定数単体集合の構成であり、任意Xの離散性の条件ではない。別の構成を定義の部分と数えない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.discrete`

:::

:::corollary "kerodon_1_1_5_11"
Kerodon Corollary 1.1.5.11（[Tag 00G0](https://kerodon.net/tag/00G0)）。対応表の状態：一部。

原文の結論の一つは const:Set→SSet の充満忠実性。IsConnected J の下の const の Full/Faithful は J=SimplexCategoryᵒᵖ へ直接適用でき、その結論成分に対応する。本質的像を離散対象とする結論は引用に含めない。

宣言：`CategoryTheory.instFullFunctorConstOfIsConnected`

:::

:::definition "kerodon_1_1_5_12" (lean := "CategoryTheory.Functor.const, SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.discrete")
Kerodon Notation 1.1.5.12（[Tag 00G1](https://kerodon.net/tag/00G1)）。対応表の状態：本体と Mathlib にある。

仮定：集合 T（Kerodon と一致）。結論：discrete T と Type 値の Functor.const は全次数で T を値とし、面・退化が恒等写像の単体集合（一致）。

:::

:::proposition "kerodon_1_1_5_14"
Kerodon Proposition 1.1.5.14（[Tag 00G3](https://kerodon.net/tag/00G3)）。対応表の状態：なし。

原文は定数対象との同型・全作用の全単射・d₀の全単射・次元0の4条件の iff。discrete/次元0/作用素を再検索。定数対象のKan性や単位対象の次元0は、任意Xに対するこの同値の方向を直接与えない。

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
Kerodon Definition 1.1.6.5（[Tag 001J](https://kerodon.net/tag/001J)）。対応表の状態：なし。

原文の Graph の射は辺を頂点へ潰す場合を含む。Prefunctor の型は二つの quiver の頂点写像と辺から辺への写像、ReflQuiver は恒等辺のデータであり、原文の非退化辺と頂点の直和上の射ではない。反射的quiverとの対応を別に構成せず同じ主張と認めない。

宣言：`Prefunctor`、`CategoryTheory.ReflQuiver`

:::

:::proposition "kerodon_1_1_6_7" (lean := "SSet.OneTruncation₂, SSet.OneTruncation₂.map")
Kerodon Proposition 1.1.6.7（[Tag 001L](https://kerodon.net/tag/001L)）。対応表の状態：Mathlib にある。

仮定：単体集合 X,Y と単体写像 f（Kerodon と一致）。結論：OneTruncation₂.map f は頂点と辺を次数別に写し、反射的 quiver の指定自己辺である頂点の退化を保存する。非退化辺の像が退化したときは原文のグラフで頂点に写る場合に当たる（一致）。

:::

:::proposition "kerodon_1_1_6_8" (uses := "kerodon_1_1_0_6, kerodon_1_1_4_12")
Kerodon Proposition 1.1.6.8（[Tag 001M](https://kerodon.net/tag/001M)）。対応表の状態：なし。

原文は次元1のXからのHomと、退化辺を頂点へ潰すGraphの射の標準写像の全単射。graph/quiver/truncation/次元1を再検索。OneTruncation₂の反射的quiver構造、SchreierGraphの同値は別の対象・写像であり、この標準Hom写像ではない。

:::

:::proposition "kerodon_1_1_6_9" (uses := "kerodon_1_1_0_6, kerodon_1_1_3_11, kerodon_1_1_6_8")
Kerodon Proposition 1.1.6.9（[Tag 001N](https://kerodon.net/tag/001N)）。対応表の状態：なし。

原文は次元≤1の充満部分圏とGraphの圏同値。graph equivalence・truncation・OneTruncationを再検索。反射的quiverの抽出だけで、原文の辺を潰せるGraphとの同値を返す宣言は見つからない。

:::

