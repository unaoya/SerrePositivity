import Verso
import VersoManual
import VersoBlueprint
import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy
import SerrePositivity.EInfinity.Hammock.WeakTensor
import SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneKanReplacement
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity
import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.Equivalence
import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorHomotopy
import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanHomotopyEquivalence
import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanSourceReplacement
import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.RelativeFunctorExtensionSpace
import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.RelativeFunctorSpace
import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.RelativeJoinPrismCell
import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.RelativeJoinPrismCoverage
import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.RelativeJoinPrismInitialPushout
import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.RelativeJoinPrismStage
import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.WeakHomotopy
import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.WeakMappingSpaces

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "3.1 The Homotopy Theory of Kan Complexes" =>
%%%
number := false
tag := "kerodon-3-1"
%%%

Kerodon の 3.1 節（[Tag 00SZ](https://kerodon.net/tag/00SZ)）の項目と、SerrePositivity・Mathlib の宣言との対応。本文は対応表（research/kerodon-coverage）の判定の理由の要約で、Kerodon の本文の写しではない。

# 3.1.1 Kan Fibrations

%%%
number := false
tag := "kerodon-3-1-1"
%%%

Kerodon [Tag 00T0](https://kerodon.net/tag/00T0)

:::definition "kerodon_3_1_1_1" (lean := "SSet.modelCategoryQuillen.fibration_iff, SSet.modelCategoryQuillen.J")
Kerodon Definition 3.1.1.1（[Tag 00T1](https://kerodon.net/tag/00T1)）。対応表の状態：Mathlib にある。

仮定：任意の単体集合の射 p : X ⟶ S（Kerodon と一致）。結論：Fibration p は、すべての次元 n\>0 とすべての番号 i のホーン包含を集めた J に対する右持ち上げ性 J.rlp p と同値（一致）。

*定義 5.3 （fibration）*

- 名前　／　包含
- Kan fibration　／　$`\Lambda^n_i\subseteq\Delta^n`（$`n\ge1`、$`0\le i\le n`）

:::

# 3.1.2 Anodyne Morphisms

%%%
number := false
tag := "kerodon-3-1-2"
%%%

Kerodon [Tag 00UG](https://kerodon.net/tag/00UG)

:::definition "kerodon_3_1_2_1" (lean := "SSet.anodyneExtensions, SSet.anodyneExtensions_eq_retracts_transfiniteCompositions")
Kerodon Definition 3.1.2.1（[Tag 00UH](https://kerodon.net/tag/00UH)）。対応表の状態：Mathlib にある。

仮定：任意の単体集合の射 f（Kerodon と一致）。結論：anodyneExtensions は、定義上は Kan fibration に対する左持ち上げ性で、J の押し出し・超限合成のレトラクトで得る弱飽和閉包と一致する（一致）。

:::

:::proposition "kerodon_3_1_2_9"
Kerodon Proposition 3.1.2.9（[Tag 014D](https://kerodon.net/tag/014D)）。対応表の状態：Mathlib にある。

仮定：単体集合の二単射と、少なくとも片方が anodyne であること（Kerodon と一致）。結論：二つの積を共通部分上で貼った押し出しから終域の積への比較包含が anodyne。左右の二通りを別の補題で与える（一致）。

宣言：`SSet.anodyneExtensions_pushoutObjObjι`、`SSet.anodyneExtensions_pushoutObjObjι'`、`SSet.anodyneExtensions_unionProd_ι`

:::

:::lemma_ "kerodon_3_1_2_10" (uses := "kerodon_1_1_0_6")
Kerodon Lemma 3.1.2.10（[Tag 00TG](https://kerodon.net/tag/00TG)）。対応表の状態：なし。

B6：anodyne 性は原文の指定射間の retract の射と往復恒等式を与えない。 候補：指定形状の積の部分複体の包含の anodyne 性は pairing で示される。ホーン包含からの指定のレトラクトは未確認。

宣言：`SSet.prodStdSimplex.anodyneExtensions_unionProd_ι`

:::

:::lemma_ "kerodon_3_1_2_11" (uses := "kerodon_1_1_0_6")
Kerodon Lemma 3.1.2.11（[Tag 03X4](https://kerodon.net/tag/03X4)）。対応表の状態：一部。

B6：isPushout\_prism\_mono\_cell は原文の和と逆像の条件から同じ押し出し正方形を直接返す。セル σ に Mono を加える場合に限定。

宣言：`SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.isPushout_prism_mono_cell`

:::

:::lemma_ "kerodon_3_1_2_12" (lean := "SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeJoinPrismStage, SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeJoinPrismCell_isPushout, SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeJoinPrismStage_top, SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeJoinPrismInitial_isPushout")
Kerodon Lemma 3.1.2.12（[Tag 00TH](https://kerodon.net/tag/00TH)）。対応表の状態：本体にある。

仮定：n : ℕ（Kerodon と一致）。結論：Δ¹×Δⁿ 内の増大列は最初が境界の積と終端面の押し出し、最後が全体で、k から k+1 は (n+1) 次元の k+1 番目のホーンの押し出し（一致）。

:::

# 3.1.3 Exponentiation for Kan Fibrations

%%%
number := false
tag := "kerodon-3-1-3"
%%%

Kerodon [Tag 00TJ](https://kerodon.net/tag/00TJ)

:::theorem "kerodon_3_1_3_1"
Kerodon Theorem 3.1.3.1（[Tag 00TK](https://kerodon.net/tag/00TK)）。対応表の状態：Mathlib にある。

仮定：単射 i : A ⟶ B、Kan fibration p : X ⟶ S と内部 Hom の指定の引き戻し（Kerodon と一致。Lean は普遍性を持つ引き戻しの選択を明示）。結論：Xᴮ から Sᴮ ×\_(Sᴬ) Xᴬ への比較射が Fibration（一致）。

宣言：`SSet.fibration_pullbackObjObjπ`

:::

:::corollary "kerodon_3_1_3_2"
Kerodon Corollary 3.1.3.2（[Tag 00TL](https://kerodon.net/tag/00TL)）。対応表の状態：Mathlib にある。

仮定：任意の単体集合 B と Kan fibration p : X ⟶ S（Kerodon と一致）。結論：p による後合成 (ihom B).map p は Fibration（一致）。

宣言：`SSet.instFibrationMapIhom`

:::

:::corollary "kerodon_3_1_3_3"
Kerodon Corollary 3.1.3.3（[Tag 00TM](https://kerodon.net/tag/00TM)）。対応表の状態：Mathlib にある。

仮定：単射 i : A ⟶ B、Kan 複体 X（Kerodon と一致）。結論：前合成 (MonoidalClosed.pre i).app X は Fibration（一致）。

宣言：`SSet.instFibrationAppPreOfMonoOfKanComplex`

:::

:::corollary "kerodon_3_1_3_4"
Kerodon Corollary 3.1.3.4（[Tag 00TN](https://kerodon.net/tag/00TN)）。対応表の状態：Mathlib にある。

仮定：任意の単体集合 B と Kan 複体 X（Kerodon と一致）。結論：内部 Hom (ihom B).obj X が KanComplex（一致）。

*定理 2.9 （$`\mathcal Kan` の射の単体的集合は Kan 複体）*

Kan 複体 $`X,Y` について、$`\mathcal Kan(X,Y)=\mathrm{Fun}(X,Y)` は Kan 複体である。

宣言：`SSet.instKanComplexObjIhom`

:::

:::theorem "kerodon_3_1_3_5"
Kerodon Theorem 3.1.3.5（[Tag 014E](https://kerodon.net/tag/014E)）。対応表の状態：一部。

B6：trivialKanFibration\_pre\_of\_anodyne は底 S が終対象のときの同じ制限射の自明 Kan 性。pullbackObjObjπ は p 自身が自明 Kan の場合も直接扱う。一般の底上の任意の Kan fibration の主張は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.trivialKanFibration_pre_of_anodyne`、`SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.trivialKanFibration_pullbackObjObjπ`

:::

:::corollary "kerodon_3_1_3_6" (lean := "SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.trivialKanFibration_pre_of_anodyne")
Kerodon Corollary 3.1.3.6（[Tag 00UT](https://kerodon.net/tag/00UT)）。対応表の状態：本体にある。

仮定：anodyne 射 i : A ⟶ B と Kan 複体 X（Kerodon と一致）。結論：Xᴮ → Xᴬ の前合成射は任意の単射に対する右持ち上げ性を持つ自明 Kan fibration（一致）。

:::

:::definition "kerodon_3_1_3_7" (lean := "SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpace, SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace")
Kerodon Construction 3.1.3.7（[Tag 01AB](https://kerodon.net/tag/01AB)）。対応表の状態：本体にある。

仮定：単体集合の写像 i, f, q, g と、両方の条件を課す場合の可換性 f≫q=i≫g（Kerodon と一致）。結論：後合成を g に固定した頂点ファイバーと、その中で i への制限を f に固定したファイバー。底を終対象とした場合に前合成だけのファイバーを得る（一致）。

*定義 10.1 （相対関手空間）*

単体的集合の射 $`r\colon K\to S`、$`q\colon X\to S` について、$`r` を $`\mathrm{Fun}(K,S)` の頂点とみて（$`K\times\Delta^0\cong K`）、ファイバー（定義 6.2）

$$`\mathrm{Fun}_{/S}(K,X)=\mathrm{Fun}(K,X)\times_{\mathrm{Fun}(K,S)}\Delta^0`

を相対関手空間という（$`q_*` の $`r` 上のファイバー。定義 2.3）。その $`n` 単体は $`q\circ f=r\circ\mathrm{pr}_K` をみたす射 $`f\colon K\times\Delta^n\to X` である。

:::

:::proposition "kerodon_3_1_3_13"
Kerodon Proposition 3.1.3.13（[Tag 01GK](https://kerodon.net/tag/01GK)）。対応表の状態：一部。

B6：relativeFunctorExtensionSpace\_isContractibleKan は同じ指定境界と底を持つ延長空間の可縮 Kan 性を直接返す。i を left anodyne とする追加仮定で、Kan fibration は left fibration でもある。一般の anodyne i 全体の後半は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre_fibration`、`SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpace_isContractibleKan`

:::

:::corollary "kerodon_3_1_3_14"
Kerodon Corollary 3.1.3.14（[Tag 01GL](https://kerodon.net/tag/01GL)）。対応表の状態：一部。

B6：anodyneExtensionChoices\_isContractibleKan は原文後半の、i が anodyne の場合の指定延長空間の可縮 Kan 性を直接返す。単射だけの場合の前半を含まない。

宣言：`SerrePositivity.KST.SConstruction.anodyneExtensionChoices_isContractibleKan`

:::

:::corollary "kerodon_3_1_3_15" (lean := "SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace_kanComplex")
Kerodon Corollary 3.1.3.15（[Tag 01GM](https://kerodon.net/tag/01GM)）。対応表の状態：本体にある。

仮定：写像 b : B ⟶ S と q : X ⟶ S（Lean が弱い：q は全ホーンの Kan fibration でなく LeftFibration で足りる）。結論：q による後合成の b 上のファイバー relativeFunctorSpace が KanComplex（一致）。

:::

# 3.1.4 Covering Maps

%%%
number := false
tag := "kerodon-3-1-4"
%%%

Kerodon [Tag 0219](https://kerodon.net/tag/0219)

:::definition "kerodon_3_1_4_1"
Kerodon Definition 3.1.4.1（[Tag 021A](https://kerodon.net/tag/021A)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。確認済み・なし。全ホーンに一意な持ち上げを要求する単体集合の被覆写像の型は未発見。位相・箙の被覆は別。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::proposition "kerodon_3_1_4_7"
Kerodon Proposition 3.1.4.7（[Tag 021G](https://kerodon.net/tag/021G)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。確認済み・なし。相対内部 Hom の Kan fibration 性はあるが、一意な持ち上げを保つ被覆版は未発見。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::corollary "kerodon_3_1_4_8"
Kerodon Corollary 3.1.4.8（[Tag 021H](https://kerodon.net/tag/021H)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。確認済み・なし。後合成の fibration 性はあるが、一意持ち上げの被覆版は未発見。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::proposition "kerodon_3_1_4_9"
Kerodon Proposition 3.1.4.9（[Tag 021J](https://kerodon.net/tag/021J)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。確認済み・なし。位相被覆と特異単体集合はあるが、特異化が一意なホーン持ち上げを保つ宣言は未発見。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::proposition "kerodon_3_1_4_12"
Kerodon Proposition 3.1.4.12（[Tag 021M](https://kerodon.net/tag/021M)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。確認済み・なし。単体写像による全引き戻し条件や、標準単体上の成分ごとの同型による被覆の特徴づけは未発見。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::corollary "kerodon_3_1_4_14"
Kerodon Corollary 3.1.4.14（[Tag 021P](https://kerodon.net/tag/021P)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。確認済み・なし。単射に対する直和成分・被覆・Kan fibration の三条件の比較は未発見。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

# 3.1.5 The Homotopy Category of Kan Complexes

%%%
number := false
tag := "kerodon-3-1-5"
%%%

Kerodon [Tag 00TR](https://kerodon.net/tag/00TR)

:::definition "kerodon_3_1_5_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex")
Kerodon Definition 3.1.5.1（[Tag 00TS](https://kerodon.net/tag/00TS)）。対応表の状態：本体にある。

仮定：任意の単体集合 X,Y と平行な射 f,g（Kerodon と一致）。結論：functorVertex が二射を内部 Hom の 0 単体に送り、SSet.π₀.mk の像の等式で同じ連結成分という関係を表せる（一致）。

:::

:::definition "kerodon_3_1_5_2" (lean := "SSet.Homotopy")
Kerodon Definition 3.1.5.2（[Tag 00TT](https://kerodon.net/tag/00TT)）。対応表の状態：Mathlib にある。

仮定：任意の単体集合 X,Y と平行な射 f₀,f₁（Kerodon と一致。相対版の部分複体は既定値 ⊥）。結論：X×Δ¹ から Y への射が両端点で f₀,f₁ となる構造（一致。Kerodon は積を Δ¹×X の順に書く）。

:::

:::proposition "kerodon_3_1_5_4" (lean := "SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy, SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge")
Kerodon Proposition 3.1.5.4（[Tag 00TU](https://kerodon.net/tag/00TU)）。対応表の状態：本体にある。

仮定：任意の単体集合 X,Y と平行な射 f,g（Kerodon と一致。Kan 性は不要）。結論：写像空間の π₀ の等式は頂点間の辺関係の対称・反射・推移閉包。各辺と向き付きの区間ホモトピーを相互に変換するため、この閉包は原文の有限列の条件を表す（一致）。

:::

:::definition "kerodon_3_1_5_9" (lean := "SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex")
Kerodon Notation 3.1.5.9（[Tag 00TX](https://kerodon.net/tag/00TX)）。対応表の状態：本体にある。

仮定：任意の単体集合の射 f : X ⟶ Y（Kerodon と一致）。結論：functorVertex f は Fun(X,Y) の 0 単体で、その SSet.π₀.mk による像が \[f\]（一致）。

:::

:::definition "kerodon_3_1_5_10" (uses := "kerodon_1_2_5_1")
Kerodon Construction 3.1.5.10（[Tag 00TY](https://kerodon.net/tag/00TY)）。対応表の状態：一部。

B6：HomotopyClasses.obj は π₀ Fun(X,Y)、pre/post は代表の合成による写像を直接構成する。Kan に対象を限れば原文の Hom と前後合成の構成成分。同じ Hom を射とする束ねた圏そのものは含まない。

宣言：`SerrePositivity.SimplicialModel.HomotopyClasses.obj`、`SerrePositivity.SimplicialModel.HomotopyClasses.pre`、`SerrePositivity.SimplicialModel.HomotopyClasses.post`

:::

# 3.1.6 The ∞-Category of Spaces

%%%
number := false
tag := "kerodon-3-1-6"
%%%

Kerodon [Tag 01YX](https://kerodon.net/tag/01YX)

*注意 （$`\mathcal S` の大きさ）*

$`\mathcal Kan` の対象は小さい Kan 複体で、その全体は $`\mathbb U` の部分集合として集合をなすが、小さくはない。したがって $`\mathcal S` は単体的集合だが小さくない。一方、小さい Kan 複体 $`X,Y` について $`\mathcal Kan(X,Y)=\mathrm{Fun}(X,Y)` は小さい（宇宙は直積と冪集合で閉じている）。

:::definition "kerodon_3_1_6_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.kanObject_simplicialCategory")
Kerodon Construction 3.1.6.1（[Tag 00TZ](https://kerodon.net/tag/00TZ)）。対応表の状態：本体にある。

仮定：固定した宇宙の単体集合（Kerodon と一致）。結論：Kan 複体を対象、内部 Hom を豊穣 Hom とする KanObject の coherent nerve が SpaceInfinity（一致。Lean の coherent nerve は Ch 2 で記録した包含順の規約）。

*定義 2.8 （Kan 複体のなす単体的圏 $`\mathcal Kan`）*

単体的圏 $`\mathcal Kan` を次で定める。

- 対象：小さい Kan 複体（定義 1.9、冒頭の規約）。

- 射の単体的集合：$`\mathcal Kan(X,Y)=\mathrm{Fun}(X,Y)`（定義 2.2）。

- 合成と恒等射：定義 2.5。

定理 2.6 によりこれは単体的圏である。

*定義 3.7 （空間の ∞ 圏 $`\mathcal S`）*

$`\mathcal S=N^{hc}(\mathcal Kan)` と定める（$`\mathcal Kan` は定義 2.8）。定理 2.9 により $`\mathcal Kan` は局所 Kan なので、定理 3.6 により $`\mathcal S` は quasicategory である。

:::

:::proposition "kerodon_3_1_6_2" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.spaceInfinity_quasicategory")
Kerodon Proposition 3.1.6.2（[Tag 01YY](https://kerodon.net/tag/01YY)）。対応表の状態：本体にある。

仮定：SpaceInfinity を作る宇宙だけ（Kerodon と一致。個別の充填性の仮定はない）。結論：SpaceInfinity が Quasicategory（一致）。

:::

:::proposition "kerodon_3_1_6_3"
Kerodon Remark 3.1.6.3（[Tag 01YZ](https://kerodon.net/tag/01YZ)）。対応表の状態：なし。

B6：包含順の coherent nerve の構成であり、原文の逆包含 nerve と低次比較への同定がない。 候補：一般の単体圏で普通 nerve から coherent nerve への写像があり、KanObject に特殊化できる。単射性と全低次単体の比較は未確認。

宣言：`SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent`

:::

:::definition "kerodon_3_1_6_9"
Kerodon Variant 3.1.6.9（[Tag 02BQ](https://kerodon.net/tag/02BQ)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。確認済み・なし。KanObject の単体的 Hom はあるが、各 Hom のホモトピー圏を持つ厳密双圏 h₂Kan は未発見。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

# 3.1.7 Homotopy Equivalences and Weak Homotopy Equivalences

%%%
number := false
tag := "kerodon-3-1-7"
%%%

Kerodon [Tag 00U1](https://kerodon.net/tag/00U1)

:::definition "kerodon_3_1_7_1" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_3_1_5_1")
Kerodon Definition 3.1.7.1（[Tag 00U2](https://kerodon.net/tag/00U2)）。対応表の状態：一部。

B6：IsSimplicialHomotopyEquivalence は同じ f,g の両合成について一段の区間ホモトピーを持つ場合を直接表す。原文の有限鎖によるホモトピーより強い仮定に限定。

*定義 13.1 （ホモトピー同値）*

Kan 複体の射 $`f\colon X\to Y` がホモトピー同値であるとは、射 $`g\colon Y\to X` と射 $`h\colon X\times\Delta^1\to X`、$`k\colon Y\times\Delta^1\to Y` で、$`h` の $`X\times\{0\}`、$`X\times\{1\}` への制限がそれぞれ $`g\circ f`、$`\mathrm{id}_X`、$`k` の $`Y\times\{0\}`、$`Y\times\{1\}` への制限がそれぞれ $`f\circ g`、$`\mathrm{id}_Y` となるものが存在することをいう。Kan 複体 $`X,Y` の間にホモトピー同値があるとき、$`X` と $`Y` はホモトピー同値であるという。

宣言：`SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence`

:::

:::proposition "kerodon_3_1_7_6" (uses := "kerodon_1_1_0_6")
Kerodon Remark 3.1.7.6（[Tag 00U5](https://kerodon.net/tag/00U5)）。対応表の状態：一部。

B6：isSimplicialHomotopyEquivalence\_of\_postcomposition\_piZero\_bijective は原文の第三条件から第一条件への向きを Kan の始域・終域に限って直接返す。三条件一般の iff は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.isSimplicialHomotopyEquivalence_of_postcomposition_piZero_bijective`、`SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence.isWeakHomotopyEquivalence`

:::

:::proposition "kerodon_3_1_7_9" (uses := "kerodon_1_1_0_6")
Kerodon Proposition 3.1.7.9（[Tag 00U8](https://kerodon.net/tag/00U8)）。対応表の状態：なし。

B6：自然変換からのホモトピーは証明部品であり、随伴関手の nerve の逆と両側ホモトピーを結論していない。 候補：自然変換から nerve の単体ホモトピーを構成する補助宣言はある。任意の左・右随伴についてのホモトピー同値の結論は未確認。

宣言：`SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHomotopy`

:::

:::proposition "kerodon_3_1_7_10" (uses := "kerodon_1_1_0_6, kerodon_1_5_5_5")
Kerodon Proposition 3.1.7.10（[Tag 00U9](https://kerodon.net/tag/00U9)）。対応表の状態：なし。

B6：切断の存在と同じ底上のホモトピーは材料。ホモトピー逆の存在をまとめる直接の結論はなく、原文の有限鎖との比較も必要。 候補：一般の自明 Kan fibration に切断があり、同じ底上の二つの持ち上げはホモトピック。一般のホモトピー同値を一つにまとめた宣言は未確認。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.trivialKanFibration_exists_section`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.exists_homotopy_over_trivialKanFibration`

:::

:::definition "kerodon_3_1_7_12" (lean := "SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence")
Kerodon Definition 3.1.7.12（[Tag 00UA](https://kerodon.net/tag/00UA)）。対応表の状態：本体にある。

仮定：任意の単体集合の射 f : X ⟶ Y（Kerodon と一致）。結論：すべての Kan 複体 Z に対して、前合成が π₀ Fun(Y,Z) から π₀ Fun(X,Z) への全単射となる述語（一致）。

:::

:::proposition "kerodon_3_1_7_13" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_3_1_7_6")
Kerodon Proposition 3.1.7.13（[Tag 00UB](https://kerodon.net/tag/00UB)）。対応表の状態：一部。

B6：前向きの型は一段のホモトピー逆を持つ f から同じ f の弱同値性を直接返す。有限鎖での逆だけより強い仮定。Kan の場合の逆向きも引用型にある。

宣言：`SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence.isWeakHomotopyEquivalence`、`SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence.isSimplicialHomotopyEquivalence`、`SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.isWeakHomotopyEquivalence_iff_isSimplicialHomotopyEquivalence`

:::

:::proposition "kerodon_3_1_7_14" (lean := "SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.homotopyEquivalence_pre_of_anodyne")
Kerodon Proposition 3.1.7.14（[Tag 00UP](https://kerodon.net/tag/00UP)）。対応表の状態：本体にある。

仮定：任意の anodyne 射 f : A ⟶ B（Kerodon と一致。引用の前合成の検査では任意の Kan 標的 Z を固定）。結論：前合成がホモトピー同値で、その π₀ 写像は全単射。anodyne 局所化で f を反転した際にも同じ f の IsWeakHomotopyEquivalence を得る（一致）。

:::

:::proposition "kerodon_3_1_7_17" (lean := "SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence.precompose_kan, SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.isWeakHomotopyEquivalence_iff_precompose_kan")
Kerodon Proposition 3.1.7.17（[Tag 03PJ](https://kerodon.net/tag/03PJ)）。対応表の状態：本体にある。

仮定：任意の単体集合の弱ホモトピー同値 f : X ⟶ Y と Kan 複体 Z（Kerodon と一致）。結論：前合成 Fun(Y,Z) → Fun(X,Z) は区間ホモトピーでの両側逆を持つ（一致。Kan 写像空間では一段のホモトピーで足りる。Lean は全 Z での条件からの逆方向も与える）。

:::

:::proposition "kerodon_3_1_7_18"
Kerodon Proposition 3.1.7.18（[Tag 00ZZ](https://kerodon.net/tag/00ZZ)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。確認済み・なし。引用は単体加群の正規化の擬同型を検査する。単体集合の自由整数鎖写像の鎖ホモトピー同値は未発見。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::proposition "kerodon_3_1_7_23" (lean := "SerrePositivity.EInfinity.Hammock.weakTensor")
Kerodon Proposition 3.1.7.23（[Tag 02L2](https://kerodon.net/tag/02L2)）。対応表の状態：本体にある。

仮定：単体集合の二写像 f,g が IsWeakHomotopyEquivalence（Kerodon と一致）。結論：点ごとの直積の写像 f ⊗ₘ g が IsWeakHomotopyEquivalence（一致）。

:::

# 3.1.8 Fibrant Replacement

%%%
number := false
tag := "kerodon-3-1-8"
%%%

Kerodon [Tag 00UU](https://kerodon.net/tag/00UU)

:::proposition "kerodon_3_1_8_1" (lean := "SerrePositivity.SimplicialModel.AnodyneKanReplacement.factorization")
Kerodon Proposition 3.1.8.1（[Tag 00UV](https://kerodon.net/tag/00UV)）。対応表の状態：本体にある。

仮定：任意の単体集合の射 f : X ⟶ Y（Kerodon と一致）。結論：anodyneExtensions と全ホーン集合 J に対する RLP の FunctorialFactorizationData。中間対象と両射は f の可換正方形に関手的（一致）。

:::

:::corollary "kerodon_3_1_8_2" (lean := "SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.anodyneKanObject, SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.anodyneKanObjectUnit_anodyne")
Kerodon Corollary 3.1.8.2（[Tag 00UW](https://kerodon.net/tag/00UW)）。対応表の状態：本体にある。

仮定：任意の単体集合 A（Kerodon と一致）。結論：anodyneKanObject A は実際の Kan 複体であり、A からの anodyne な単位射を持つ（一致）。

:::

:::corollary "kerodon_3_1_8_5" (lean := "SSet.anodyneExtensions, SSet.anodyneExtensions_eq_llp_rlp")
Kerodon Corollary 3.1.8.5（[Tag 00X8](https://kerodon.net/tag/00X8)）。対応表の状態：Mathlib にある。

仮定：任意の単体集合の射 f（Kerodon と一致）。結論：anodyneExtensions f と J.rlp の全射に対する左持ち上げ性が同値。J.rlp は Kan fibration のクラス（一致）。

:::

:::proposition "kerodon_3_1_8_6"
Kerodon Proposition 3.1.8.6（[Tag 012U](https://kerodon.net/tag/012U)）。対応表の状態：なし。

B6：引用は anodyne を反転する SSet 上の関手。原文は Kan 上の任意の関手で、二つの条件のいずれの含意も引用の結論ではない。 候補：SSet 上で anodyne を反転する関手はホモトピックな射を同じ射へ送る。Kan 上の関手の二条件の同値は未確認。

宣言：`SerrePositivity.SimplicialModel.AnodyneHomotopy.map_homotopy_eq`

:::

:::corollary "kerodon_3_1_8_7"
Kerodon Corollary 3.1.8.7（[Tag 012V](https://kerodon.net/tag/012V)）。対応表の状態：なし。

B6：homEquiv は対象ごとの局所化 Hom の比較で、原文の関手圏間の同型の構成ではない。 候補：anodyne 局所化で Kan 標的への射をホモトピー類と比較。hKan からの関手圏の指定同型は未発見。

宣言：`SerrePositivity.SimplicialModel.KanLocalizedRepresentatives.homEquiv`

:::

:::definition "kerodon_3_1_8_8"
Kerodon Variant 3.1.8.8（[Tag 012W](https://kerodon.net/tag/012W)）。対応表の状態：なし。

B6：自明 fibration の反転と局所化 Hom の比較は、指定の関手圏の同値という結論の成分でなく材料。 候補：anodyne 局所化の射の比較と自明 Kan fibration の反転はある。弱同値を反転する関手の圏と Fun(hKan,C) の同値は未確認。

宣言：`SerrePositivity.SimplicialModel.KanLocalizedRepresentatives.homEquiv`、`SerrePositivity.KST.SConstruction.map_isIso_of_trivialKanFibration`

:::

:::definition "kerodon_3_1_8_12" (uses := "kerodon_1_1_0_6, kerodon_3_1_8_1")
Kerodon Variant 3.1.8.12（[Tag 050L](https://kerodon.net/tag/050L)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。確認済み・なし。全ホーンの分解はあるが、閾値より高次のホーンだけを添付し低次の単体を保つ分解は未発見。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

