import Verso
import VersoManual
import VersoBlueprint
import Mathlib.AlgebraicTopology.SimplicialCategory.Basic
import Mathlib.CategoryTheory.Enriched.Basic
import Mathlib.GroupTheory.Coxeter.Basic
import Mathlib.GroupTheory.Coxeter.Length
import Mathlib.GroupTheory.Coxeter.Matrix
import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.Cube
import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.Quasicategory

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "2.4 Simplicial Categories" =>
%%%
number := false
tag := "kerodon-2-4"
%%%

Kerodon の 2.4 節（[Tag 00JN](https://kerodon.net/tag/00JN)）の項目と、SerrePositivity・Mathlib の宣言との対応。本文は対応表（research/kerodon-coverage）の判定の理由の要約で、Kerodon の本文の写しではない。

# 2.4.1 Simplicial Enrichment

%%%
number := false
tag := "kerodon-2-4-1"
%%%

Kerodon [Tag 00JQ](https://kerodon.net/tag/00JQ)

:::definition "kerodon_2_4_1_1" (lean := "CategoryTheory.SimplicialCategory, CategoryTheory.SimplicialCategory.sHom")
Kerodon Definition 2.4.1.1（[Tag 00JR](https://kerodon.net/tag/00JR)）。対応表の状態：Mathlib にある。

仮定：対象型 C（Kerodon と一致。Lean では Hom の 0 単体から得る普通圏の構造も入力し、豊穣化との整合を課す）。結論：各組の単体集合 sHom、積からの合成と単位、結合・単位条件を備える（一致）。

:::

:::definition "kerodon_2_4_1_3" (uses := "kerodon_1_1_0_6")
Kerodon Construction 2.4.1.3（[Tag 00JT](https://kerodon.net/tag/00JT)）。対応表の状態：一部。

B6：homEquiv' は n=0 で Hom 集合を sHom の0単体に同一視する成分を直接与える。全次数での圏と単体的演算の一式は未確認。

宣言：`CategoryTheory.SimplicialCategory.homEquiv'`

:::

:::definition "kerodon_2_4_1_6"
Kerodon Definition 2.4.1.6（[Tag 00JW](https://kerodon.net/tag/00JW)）。対応表の状態：一部。

B6：sHom の0単体を homEquiv' で指定し Edge を取ると、d₁=f,d₀=g という原文のホモトピーのデータを直接表す。専用の名前付き述語や合成法は含まない。

宣言：`SSet.Edge`、`CategoryTheory.SimplicialCategory.homEquiv'`

:::

:::definition "kerodon_2_4_1_8" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1")
Kerodon Definition 2.4.1.8（[Tag 00JY](https://kerodon.net/tag/00JY)）。対応表の状態：なし。

B6：simplicialNerve\_quasicategory は局所 Kan 性を入力仮定として使う定理。その仮定から局所 Kan の定義を表す宣言を取り出せるわけではなく、結論は nerve の準圏性という別の主張。

宣言：`SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialNerve_quasicategory`

:::

:::definition "kerodon_2_4_1_11" (lean := "CategoryTheory.EnrichedFunctor")
Kerodon Definition 2.4.1.11（[Tag 00K1](https://kerodon.net/tag/00K1)）。対応表の状態：Mathlib にある。

仮定：単体集合で豊穣化した C, D（Kerodon と一致。EnrichedFunctor は任意の基礎モノイダル圏 V でも使える）。結論：対象の写像と各 Hom の単体写像が豊穣合成と恒等を保存する（一致）。

:::

:::proposition "kerodon_2_4_1_13"
Kerodon Proposition 2.4.1.13（[Tag 00K3](https://kerodon.net/tag/00K3)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。一般の EnrichedCat は双圏。Cat\_Δ の小極限と小余極限のインスタンスは未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。

:::

# 2.4.3 The Homotopy Coherent Nerve

%%%
number := false
tag := "kerodon-2-4-3"
%%%

Kerodon [Tag 00KM](https://kerodon.net/tag/00KM)

:::definition "kerodon_2_4_3_1" (uses := "kerodon_2_3_5_1")
Kerodon Notation 2.4.3.1（[Tag 00KN](https://kerodon.net/tag/00KN)）。対応表の状態：なし。

B6：原文は逆包含順の有限鎖の nerve。SimplicialThickening と pathInteriorEquiv は包含順の別模型で、次数・合成を保つ原文との比較がないため、その模型の同型だけでは partial にしない。

宣言：`CategoryTheory.SimplicialThickening`、`SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.path_hom_iff`、`SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathInteriorEquiv`

:::

:::definition "kerodon_2_4_3_5" (uses := "kerodon_1_1_0_6")
Kerodon Definition 2.4.3.5（[Tag 00KS](https://kerodon.net/tag/00KS)）。対応表の状態：なし。

B6：SimplicialNerve の定義域は包含順の thickening。原文の逆包含 Path による関手集合との比較が単体構造まで必要で、似た nerve の定義だけでは原文の構成を直接得ない。

宣言：`CategoryTheory.SimplicialNerve`

:::

# 2.4.4 The Path Category of a Simplicial Set

%%%
number := false
tag := "kerodon-2-4-4"
%%%

Kerodon [Tag 00L0](https://kerodon.net/tag/00L0)

:::definition "kerodon_2_4_4_1" (uses := "kerodon_1_1_0_6")
Kerodon Definition 2.4.4.1（[Tag 00L1](https://kerodon.net/tag/00L1)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。S から coherent nerve への写像を表現する path 圏の普遍性の型は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。

:::

:::definition "kerodon_2_4_4_2" (uses := "kerodon_1_1_0_6")
Kerodon Notation 2.4.4.2（[Tag 00L2](https://kerodon.net/tag/00L2)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。任意の単体集合 S からの Path\[S\] の構成は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。

:::

:::proposition "kerodon_2_4_4_3"
Kerodon Proposition 2.4.4.3（[Tag 00L3](https://kerodon.net/tag/00L3)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。任意 S の path 圏の存在は未発見。coherentResolution の値域は SSet。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。

:::

:::corollary "kerodon_2_4_4_4"
Kerodon Corollary 2.4.4.4（[Tag 00L4](https://kerodon.net/tag/00L4)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。coherent nerve の左随伴 ℭ : SSet → Cat\_Δ は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。

:::

:::proposition "kerodon_2_4_4_7"
Kerodon Proposition 2.4.4.7（[Tag 00L7](https://kerodon.net/tag/00L7)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。自由パス圏はあるが、グラフから定数単体圏への指定写像が path 圏の普遍性を満たす宣言は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。

:::

:::definition "kerodon_2_4_4_9" (uses := "kerodon_1_1_0_6")
Kerodon Notation 2.4.4.9（[Tag 00L9](https://kerodon.net/tag/00L9)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。非退化単体と端点を指定した減少部分集合列の組 E(S,m) は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。

:::

:::theorem "kerodon_2_4_4_10" (uses := "kerodon_1_1_0_6, kerodon_1_2_3_13, kerodon_1_3_7_7, kerodon_2_4_4_9, kerodon_2_4_4_16")
Kerodon Theorem 2.4.4.10（[Tag 00LA](https://kerodon.net/tag/00LA)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。任意 S の path 圏からの豊穣関手を E(S,m) によるデータで特徴づける定理は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。

:::

:::proposition "kerodon_2_4_4_13"
Kerodon Proposition 2.4.4.13（[Tag 00LC](https://kerodon.net/tag/00LC)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。1骨格からの因子化と、自由パス圏から Path\[S\]₀ への同型は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。

:::

:::proposition "kerodon_2_4_4_15" (uses := "kerodon_1_1_0_6, kerodon_2_4_4_1")
Kerodon Proposition 2.4.4.15（[Tag 00LE](https://kerodon.net/tag/00LE)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。一般の半順序 Q の Path\[Q\] が N(Q) に対し普遍性を満たす定理は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。

:::

:::lemma_ "kerodon_2_4_4_16" (uses := "kerodon_1_3_7_8, kerodon_1_3_7_11, kerodon_2_4_4_9")
Kerodon Lemma 2.4.4.16（[Tag 00LF](https://kerodon.net/tag/00LF)）。対応表の状態：なし。

B6：pathPrefix/pathSuffix は経路の部分集合の切り分けという証明部品。原文は指定の u が三つの条件を満たす主張で、いずれの条件もこれらの型の結論ではない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathPrefix`、`SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathSuffix`

:::

:::corollary "kerodon_2_4_4_18"
Kerodon Corollary 2.4.4.18（[Tag 0324](https://kerodon.net/tag/0324)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。途中点の上下の path 圏からの豊穣圏の押し出しの比較は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。

:::

:::corollary "kerodon_2_4_4_20"
Kerodon Corollary 2.4.4.20（[Tag 0326](https://kerodon.net/tag/0326)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。上下の押し出しを Path\[Q\] に入れる関手の一意な左逆は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。

:::

# 2.4.5 From Simplicial Categories to ∞-Categories

%%%
number := false
tag := "kerodon-2-4-5"
%%%

Kerodon [Tag 00LH](https://kerodon.net/tag/00LH)

:::theorem "kerodon_2_4_5_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialNerve_quasicategory")
Kerodon Theorem 2.4.5.1（[Tag 00LJ](https://kerodon.net/tag/00LJ)）。対応表の状態：本体にある。

仮定：単体圏 C で、任意の X,Y の sHom X Y が KanComplex（Kerodon と一致）。結論：SimplicialNerve C が Quasicategory、すなわちすべての内角を充填する（一致）。

:::

:::definition "kerodon_2_4_5_2" (lean := "SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube, SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cubeSplitIso")
Kerodon Notation 2.4.5.2（[Tag 00LK](https://kerodon.net/tag/00LK)）。対応表の状態：本体にある。

仮定：任意の座標集合 I（Kerodon と一致）。結論：部分集合を包含で順序づけた Set I の nerve として I 立方体を得る。任意の座標 i の分離は残りの立方体と Δ¹ の積への同型（一致）。

:::

:::proposition "kerodon_2_4_5_4" (uses := "kerodon_1_1_0_6")
Kerodon Remark 2.4.5.4（[Tag 00LM](https://kerodon.net/tag/00LM)）。対応表の状態：なし。

B6：pathInteriorNerveIso は包含順の path と内部点集合の包含順の nerve の同型。原文の逆包含から補集合で得る特定同型・合成式との比較を含まないため別模型として none。

宣言：`SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathInteriorNerveIso`、`SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathInteriorEquiv`

:::

:::definition "kerodon_2_4_5_5" (uses := "kerodon_1_1_0_6, kerodon_2_4_5_2")
Kerodon Notation 2.4.5.5（[Tag 00LN](https://kerodon.net/tag/00LN)）。対応表の状態：一部。

B6：cubeBoundary の一定座標条件は全ての面の和という原文の境界を直接表す。hollowCube は指定座標の下面を欠く側だけで、二種類の hollow cube の両方は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cubeBoundary`、`SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hollowCube`

:::

:::proposition "kerodon_2_4_5_8" (uses := "kerodon_1_1_0_6, kerodon_2_4_4_10, kerodon_2_4_4_16, kerodon_2_4_5_4, kerodon_2_4_5_5")
Kerodon Proposition 2.4.5.8（[Tag 00LR](https://kerodon.net/tag/00LR)）。対応表の状態：なし。

B6：pathThrough/pathFaceIso は包含順の経路部分の部品で、hornHollowHom\_extension の結論も Hom への延長。原文の Path\[Λ\]→Path\[Δ\] という特定関手の (a)〜(c) は直接述べない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough`、`SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathFaceIso`、`SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornHollowHom_extension`

:::

:::proposition "kerodon_2_4_5_9"
Kerodon Proposition 2.4.5.9（[Tag 00LS](https://kerodon.net/tag/00LS)）。対応表の状態：なし。

B6：hornCompositionHom\_composition\_overlap は内角から作る Hom の面の整合性。任意の E と D の豊穣関手の延長集合の全単射とは対象・結論が異なる証明部品。

宣言：`SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornCompositionHom_composition_overlap`

:::

:::corollary "kerodon_2_4_5_10" (uses := "kerodon_1_1_0_6")
Kerodon Corollary 2.4.5.10（[Tag 00LT](https://kerodon.net/tag/00LT)）。対応表の状態：なし。

B6：hornFilledFunctor と面の等式は包含順模型の充填関手を作るが、逆包含模型の指定の λ₀ とその制限条件を同一視する宣言がない。原文の全単射の方向とはまだ数えない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornHollowHom_extension`、`SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornFilledFunctor`、`SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornFilledFunctor_face`

:::

:::theorem "kerodon_2_4_5_11"
Kerodon Theorem 2.4.5.11（[Tag 00LU](https://kerodon.net/tag/00LU)）。対応表の状態：一部。

B6：intervalEndpoint\_zero\_trivialKanFibration と kanIntervalEvaluation\_trivialKanFibration は Kan X から各端点評価が自明 Kan fibration となる向き。各評価の性質から Kan 性を得る逆向きは含まない。

宣言：`SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalEndpoint_zero_trivialKanFibration`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanIntervalEvaluation_trivialKanFibration`

:::

:::corollary "kerodon_2_4_5_12"
Kerodon Corollary 2.4.5.12（[Tag 00LV](https://kerodon.net/tag/00LV)）。対応表の状態：一部。

B6：hollowCube\_extension は指定座標の下面を欠く hollow cube から Kan X への任意の写像の延長を直接与える。原文の二つの延長のうち上面を含む側のみ。

宣言：`SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hollowCube_extension`、`SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hollowCube_anodyne`、`SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hollowCylinder_anodyne`

:::

# 2.4.6 The Homotopy Category of a Simplicial Category

%%%
number := false
tag := "kerodon-2-4-6"
%%%

Kerodon [Tag 00LW](https://kerodon.net/tag/00LW)

:::definition "kerodon_2_4_6_1"
Kerodon Construction 2.4.6.1（[Tag 00LX](https://kerodon.net/tag/00LX)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。個々の sHom の π₀ は使われるが、それらを Hom とする単体圏のホモトピー圏の構成は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。

:::

:::proposition "kerodon_2_4_6_7"
Kerodon Proposition 2.4.6.7（[Tag 00M2](https://kerodon.net/tag/00M2)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。成分の比較補題はあるが、離散的な単体圏への関手を hC で一意に因子化する宣言は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。

:::

:::corollary "kerodon_2_4_6_8"
Kerodon Corollary 2.4.6.8（[Tag 00M3](https://kerodon.net/tag/00M3)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。普通圏を定数単体圏とする包含への左随伴 h は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。

:::

:::proposition "kerodon_2_4_6_9"
Kerodon Proposition 2.4.6.9（[Tag 00M4](https://kerodon.net/tag/00M4)）。対応表の状態：なし。

B6：頂点・辺の全単射とホモトピー類の等式は比較を作る材料だが、原文の特定の U による圏同型の部分結論ではない。包含順/逆包含の nerve の比較も必要。

宣言：`SerrePositivity.EInfinity.Hammock.coherentEdge_homMk_eq_of_homotopy`、`SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdgeEquiv`、`SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertexEquiv`

:::

:::proposition "kerodon_2_4_6_10" (uses := "kerodon_1_1_0_6, kerodon_2_4_6_13")
Kerodon Proposition 2.4.6.10（[Tag 00M5](https://kerodon.net/tag/00M5)）。対応表の状態：なし。

B6：coherentTriangleMappingEdge は長辺 h から合成 f≫g への辺で、原文は合成から h へのホモトピー。一般の Hom は Kan とも仮定しないので向きを反転できず、定値合成三角形だけも指定全単射を与えない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct`、`SerrePositivity.KST.SConstruction.coherentTriangleMappingEdge`

:::

:::proposition "kerodon_2_4_6_12"
Kerodon Proposition 2.4.6.12（[Tag 00M7](https://kerodon.net/tag/00M7)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。内角の空洞立方体の補題はあるが、境界包含に沿う Path の全 Hom と境界立方体の表示は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。

:::

:::corollary "kerodon_2_4_6_13" (uses := "kerodon_1_1_0_6")
Kerodon Corollary 2.4.6.13（[Tag 00M8](https://kerodon.net/tag/00M8)）。対応表の状態：なし。

B6：次元2の候補も長辺から合成への逆向きの辺であり、原文の立方体境界の特定の λ₀ に沿う延長と同一視できない。次元特殊化だけではこの差は解消しない。

宣言：`SerrePositivity.KST.SConstruction.coherentTriangleMappingEdge`

:::

:::definition "kerodon_2_4_6_16"
Kerodon Construction 2.4.6.16（[Tag 02BJ](https://kerodon.net/tag/02BJ)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。豊穣 Hom のホモトピー圏を Hom 圏とする h₂C は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。

:::

:::proposition "kerodon_2_4_6_21"
Kerodon Proposition 2.4.6.21（[Tag 02BP](https://kerodon.net/tag/02BP)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。h₂C の指定写像に沿う単体関手の一意因子化は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。

:::

# 2.4.7 Example: Braid Monoids

%%%
number := false
tag := "kerodon-2-4-7"
%%%

Kerodon [Tag 00MZ](https://kerodon.net/tag/00MZ)

:::definition "kerodon_2_4_7_1" (lean := "CoxeterSystem, CoxeterMatrix")
Kerodon Definition 2.4.7.1（[Tag 00N0](https://kerodon.net/tag/00N0)）。対応表の状態：Mathlib にある。

仮定：群 W と生成元を添字づける型 B（Kerodon と一致。積の位数は CoxeterMatrix に持たせ、無限位数を 0 と記す）。結論：Coxeter 行列の表示で定めた群から W への生成元を指定する同型を与える型（一致）。

:::

:::definition "kerodon_2_4_7_3" (lean := "CoxeterSystem.length")
Kerodon Notation 2.4.7.3（[Tag 00N2](https://kerodon.net/tag/00N2)）。対応表の状態：Mathlib にある。

仮定：CoxeterMatrix M に対する CoxeterSystem M W と w : W（Kerodon と一致）。結論：w を指定生成元の積で表す語のうち最短の長さを Nat で返す（一致）。

:::

:::definition "kerodon_2_4_7_5"
Kerodon Construction 2.4.7.5（[Tag 00N4](https://kerodon.net/tag/00N4)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。Coxeter 群内の braid word の等式はあるが、二乗関係を外した Artin 群と正モノイドの構成は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。

:::

:::definition "kerodon_2_4_7_6"
Kerodon Notation 2.4.7.6（[Tag 00N5](https://kerodon.net/tag/00N5)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。非単位元の自由モノイドに、積と長さの加法性で決まる細分順序を入れた単体モノイドは未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。

:::

:::theorem "kerodon_2_4_7_9"
Kerodon Theorem 2.4.7.9（[Tag 00N8](https://kerodon.net/tag/00N8)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。有限 Coxeter 系の正 braid モノイドに対する Deligne の主張は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。

:::

:::definition "kerodon_2_4_7_10"
Kerodon Notation 2.4.7.10（[Tag 00N9](https://kerodon.net/tag/00N9)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。群の普通 nerve はあるが、長さ加法性で切り出した B°W は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。

:::

:::definition "kerodon_2_4_7_11"
Kerodon Construction 2.4.7.11（[Tag 00NA](https://kerodon.net/tag/00NA)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。長さ加法的な語を区間ごとの積へ送り、BM(W) の coherent nerve に入れる写像は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。

:::

:::proposition "kerodon_2_4_7_12"
Kerodon Proposition 2.4.7.12（[Tag 00NB](https://kerodon.net/tag/00NB)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。BM(W) が B°W の path 圏を表す普遍性は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。

:::

:::corollary "kerodon_2_4_7_13"
Kerodon Corollary 2.4.7.13（[Tag 00NC](https://kerodon.net/tag/00NC)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。Path\[B°W\] の自己射単体モノイドと正 braid モノイドの弱ホモトピー同値は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。

:::

