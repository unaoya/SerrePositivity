import Verso
import VersoManual
import VersoBlueprint
import Mathlib.AlgebraicTopology.Quasicategory.InnerFibration
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpaceLeft
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpaceRightKan

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "5.4 ∞-Bicategories" =>
%%%
number := false
tag := "kerodon-5-4"
%%%

Kerodon の 5.4 節（[Tag 01W4](https://kerodon.net/tag/01W4)）の項目と、SerrePositivity・Mathlib の宣言との対応。本文は対応表（research/kerodon-coverage）の判定の理由の要約で、Kerodon の本文の写しではない。

# 5.4.1 Definitions

%%%
number := false
tag := "kerodon-5-4-1"
%%%

Kerodon [Tag 01W6](https://kerodon.net/tag/01W6)

:::definition "kerodon_5_4_1_1" (uses := "kerodon_1_1_0_6")
Kerodon Definition 5.4.1.1（[Tag 01W9](https://kerodon.net/tag/01W9)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：局所 Kan の hc nerve・普通の双圏・Duskin・薄さ付きの内外ホーンを照合。外ホーンの指定された薄い三角形条件を含む ∞-bicategory の定義。Quasicategory は内ホーン、Mathlib の Bicategory は対象・1射・2射の構造。

:::

:::proposition "kerodon_5_4_1_2"
Kerodon Proposition 5.4.1.2（[Tag 01WA](https://kerodon.net/tag/01WA)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：局所 Kan の hc nerve・普通の双圏・Duskin・薄さ付きの内外ホーンを照合。任意の ∞ 圏が ∞-bicategory の公理を満たす含意。通常圏の Bicategory インスタンスは単体集合のホーン条件を述べない。

:::

:::proposition "kerodon_5_4_1_5"
Kerodon Proposition 5.4.1.5（[Tag 01WD](https://kerodon.net/tag/01WD)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：局所 Kan の hc nerve・普通の双圏・Duskin・薄さ付きの内外ホーンを照合。Duskin nerve の ∞-bicategory 公理。局所 Kan な simplicial category の coherent nerve の Quasicategory は別の nerve と仮定。

:::

# 5.4.2 Interior Fibrations

%%%
number := false
tag := "kerodon-5-4-2"
%%%

Kerodon [Tag 01WF](https://kerodon.net/tag/01WF)

:::definition "kerodon_5_4_2_1" (lean := "SSet.InnerFibration") (uses := "kerodon_1_1_0_6")
Kerodon Definition 5.4.2.1（[Tag 01WG](https://kerodon.net/tag/01WG)）。対応表の状態：一部。

*主張*　無限双圏 $`D` への単体集合の射 $`q:C\to D` は、内部角の欠けた頂点の前後三頂点が底で薄い二単体をなす場合に持ち上げが存在し、全退化辺が $`q`-デカルトかつ $`q`-余デカルトであるとき interior fibration である。

InnerFibrationは全inner hornの持ち上げを要求するので、原文の第一条件（像の隣接三角形がthinの場合のinner horn持ち上げ）を直接与える。第二条件の全恒等辺のcartesian/cocartesian性をこの型だけから数えず、定義全体とのiffではない。

:::

:::lemma_ "kerodon_5_4_2_6" (uses := "kerodon_1_1_0_6")
Kerodon Lemma 5.4.2.6（[Tag 01WM](https://kerodon.net/tag/01WM)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：∞ 圏の場合の内ファイブレーション・左右 pinched の比較・通常双圏と薄い 2 面を照合。interior fibration が像で薄い 2-単体を反映する主張。thin nerve の「thin」は通常圏の射の一意性を指す。

:::

:::proposition "kerodon_5_4_2_8" (uses := "kerodon_1_1_0_6, kerodon_5_4_1_1, kerodon_5_4_2_6")
Kerodon Proposition 5.4.2.8（[Tag 01WP](https://kerodon.net/tag/01WP)）。対応表の状態：なし。

引用は準圏性まで。原文の∞-bicategoryはthinな2単体の条件と指定退化面を持つ外hornの延長も課し、準圏の内horn充填性の型だけがその全条件を直接返すわけではない。準圏から∞-bicategoryへの比較を欠く。

宣言：`SSet.quasicategory_of_innerFibration`

:::

:::proposition "kerodon_5_4_2_9"
Kerodon Proposition 5.4.2.9（[Tag 01WQ](https://kerodon.net/tag/01WQ)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：∞ 圏の場合の内ファイブレーション・左右 pinched の比較・通常双圏と薄い 2 面を照合。interior fibration が合成に閉じること。Mathlib の Fibration.comp はモデル圏の射クラスの閉性。

:::

:::proposition "kerodon_5_4_2_10"
Kerodon Proposition 5.4.2.10（[Tag 01WR](https://kerodon.net/tag/01WR)）。対応表の状態：なし。

pinchedHomMap\_rightFibrationは右pinched模型の射のright fibration性。原文の右模型はleft、左模型はrightという二結論であり、左右の対応・反転した射を比較する型なしには同じ射の結論ではない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomMap_rightFibration`

:::

# 5.4.3 Slices of ∞-Bicategories

%%%
number := false
tag := "kerodon-5-4-3"
%%%

Kerodon [Tag 01WT](https://kerodon.net/tag/01WT)

:::proposition "kerodon_5_4_3_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceOverProjection_rightFibration, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceUnderProjection_leftFibration") (uses := "kerodon_1_1_0_6, kerodon_5_4_3_8")
Kerodon Proposition 5.4.3.1（[Tag 01WU](https://kerodon.net/tag/01WU)）。対応表の状態：一部。

*主張*　無限双圏 $`C` の任意の単体図式 $`f:K\to C` に対し、スライスと余スライスから $`C` への射影は interior fibration である。

Cを準圏に強めるとslice/coslice射影はそれぞれright/left fibration、従ってinner fibrationであり、原文の指定した二射のinterior horn持ち上げ条件を直接満たす。

:::

:::corollary "kerodon_5_4_3_4" (uses := "kerodon_1_1_0_6, kerodon_5_4_2_8, kerodon_5_4_3_1")
Kerodon Corollary 5.4.3.4（[Tag 01WX](https://kerodon.net/tag/01WX)）。対応表の状態：なし。

引用は準圏性まで。原文の∞-bicategoryはthinな2単体の条件と指定退化面を持つ外hornの延長も課し、準圏の内horn充填性の型だけがその全条件を直接返すわけではない。準圏から∞-bicategoryへの比較を欠く。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceOver_quasicategory`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceUnder_quasicategory`

:::

:::corollary "kerodon_5_4_3_5" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHom_kanComplex, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft_kanComplex")
Kerodon Corollary 5.4.3.5（[Tag 01WY](https://kerodon.net/tag/01WY)）。対応表の状態：一部。

*主張*　無限双圏の任意の二対象に対して、左と右の pinched 射空間は無限圏である。

Cを準圏に強めるとpinchedHomとpinchedHomLeftはともにKan、従って準圏であり、原文の二つのpinched写像空間の結論を直接満たす。

:::

:::proposition "kerodon_5_4_3_8" (uses := "kerodon_1_1_0_6, kerodon_4_3_6_16")
Kerodon Proposition 5.4.3.8（[Tag 01X1](https://kerodon.net/tag/01X1)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：∞ 圏で slice/coslice の特例・左右 pinched の Kan 性・薄い 2 面を固定した joinを照合。K₀⊂K に沿う slice 比較の指定ホーン持ち上げから薄い三角形を固定した join の充填を得る結論。通常の join anodyne は薄さを要求しない。

:::

:::proposition "kerodon_5_4_3_9" (uses := "kerodon_1_1_0_6")
Kerodon Proposition 5.4.3.9（[Tag 01X3](https://kerodon.net/tag/01X3)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：∞ 圏で slice/coslice の特例・左右 pinched の Kan 性・薄い 2 面を固定した joinを照合。指定した頂点からの三角形の薄さを課した slice 射影の持ち上げ。right fibration の普遍性では個別三角形の薄さが指定されない。

:::

:::proposition "kerodon_5_4_3_11"
Kerodon Proposition 5.4.3.11（[Tag 01X5](https://kerodon.net/tag/01X5)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：∞ 圏で slice/coslice の特例・左右 pinched の Kan 性・薄い 2 面を固定した joinを照合。K₀ に固定した slice 比較で Δ¹⋆\{x\} の三角形条件を満たす延長。quasicategory の restriction の型には薄い条件がない。

:::

# 5.4.4 The Local Thinness Criterion

%%%
number := false
tag := "kerodon-5-4-4"
%%%

Kerodon [Tag 01X7](https://kerodon.net/tag/01X7)

:::theorem "kerodon_5_4_4_1" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_5_1_1_1, kerodon_5_4_3_8")
Kerodon Theorem 5.4.4.1（[Tag 01X8](https://kerodon.net/tag/01X8)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：∞ 圏で薄さを自動化・左右 slice の条件・普通の双圏の 2-cellを照合。薄い 2-単体と各 slice/coslice での局所 cartesian・cocartesian 条件等の同値。通常の辺の cartesian 性は ∞-bicategory の三角形を分類しない。

:::

:::corollary "kerodon_5_4_4_2" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_5_1_1_1, kerodon_5_4_3_1, kerodon_5_4_3_8, kerodon_5_4_3_9, kerodon_5_4_4_1")
Kerodon Corollary 5.4.4.2（[Tag 01X9](https://kerodon.net/tag/01X9)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：∞ 圏で薄さを自動化・左右 slice の条件・普通の双圏の 2-cellを照合。slice の辺 u に対する局所 cartesian 性を元の三角形の薄さで判定。isCartesianEdge の通常の pullback には元の薄さの述語がない。

:::

# 5.4.5 The Pith of an ∞-Bicategory

%%%
number := false
tag := "kerodon-5-4-5"
%%%

Kerodon [Tag 01XA](https://kerodon.net/tag/01XA)

:::definition "kerodon_5_4_5_1"
Kerodon Construction 5.4.5.1（[Tag 01XB](https://kerodon.net/tag/01XB)）。対応表の状態：なし。

通常双圏のPithという型と、原文の単体的∞-bicategoryの全2面がthinとなる部分複体とのnerve比較を欠く。同名の類似構成だけでは数えない。

宣言：`CategoryTheory.Bicategory.Pith`

:::

:::proposition "kerodon_5_4_5_6" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_5_4_1_1, kerodon_5_4_5_10")
Kerodon Proposition 5.4.5.6（[Tag 01XG](https://kerodon.net/tag/01XG)）。対応表の状態：なし。

MathlibのPithの各Homがgroupoidという型は通常双圏のもの。原文の指定単体的pithが準圏という結論へ移す比較がない。

宣言：`CategoryTheory.Bicategory.Pith.homGroupoid`

:::

:::definition "kerodon_5_4_5_7" (uses := "kerodon_1_1_0_6")
Kerodon Definition 5.4.5.7（[Tag 01XH](https://kerodon.net/tag/01XH)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：普通の双圏 Pith・∞ 圏 core と反対・局所 Kan と薄い面を照合。3-単体の指定 2-面に対する inner exchange の述語。三角形での cartesian 辺の合成には 2-面の所属条件がない。

:::

:::proposition "kerodon_5_4_5_10" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_5_1_2_4, kerodon_5_4_3_1, kerodon_5_4_4_1, kerodon_5_4_5_7")
Kerodon Proposition 5.4.5.10（[Tag 01XL](https://kerodon.net/tag/01XL)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：普通の双圏 Pith・∞ 圏 core と反対・局所 Kan と薄い面を照合。薄い三角形全体が inner exchange を満たす結論。通常圏での可換三角形と任意の ∞-bicategory の薄い 2-面を区別した。

:::

:::definition "kerodon_5_4_5_12" (uses := "kerodon_1_4_0_1")
Kerodon Definition 5.4.5.12（[Tag 047R](https://kerodon.net/tag/047R)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：普通の双圏 Pith・∞ 圏 core と反対・局所 Kan と薄い面を照合。Pith(C) を介して定める ∞-bicategory の同型辺。IsInvertibleEdge の型だけでは Pith に属するという定義を与えない。

:::

:::proposition "kerodon_5_4_5_13"
Kerodon Proposition 5.4.5.13（[Tag 01XN](https://kerodon.net/tag/01XN)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：普通の双圏 Pith・∞ 圏 core と反対・局所 Kan と薄い面を照合。Pith の左右 pinched Hom と元の pinched Hom の core の厳密な同型。一般の左右 pinched 比較は pith と core の交換を述べない。

:::

:::proposition "kerodon_5_4_5_14" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_5_1_1_1, kerodon_5_1_4_1, kerodon_5_4_3_9, kerodon_5_4_4_2, kerodon_5_4_5_6")
Kerodon Proposition 5.4.5.14（[Tag 01XP](https://kerodon.net/tag/01XP)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：普通の双圏 Pith・∞ 圏 core と反対・局所 Kan と薄い面を照合。slice と Pith の pullback の内ファイブレーション性と薄さを用いる辺の判定。一般の Pith を持たない slice の射影型とは異なる。

:::

# 5.4.6 The Four-out-of-Five Property

%%%
number := false
tag := "kerodon-5-4-6"
%%%

Kerodon [Tag 01XQ](https://kerodon.net/tag/01XQ)

:::definition "kerodon_5_4_6_1"
Kerodon Definition 5.4.6.1（[Tag 01XR](https://kerodon.net/tag/01XR)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の同型・弱同値の合成・∞ 圏の可逆辺・薄い面と 4 単体を照合。3-単体で二つの合成辺の所属から六つの辺の所属を要求する述語。MorphismProperty.HasTwoOutOfThreeProperty は三辺の条件。

:::

:::proposition "kerodon_5_4_6_5" (uses := "kerodon_1_4_0_1, kerodon_1_4_6_1")
Kerodon Proposition 5.4.6.5（[Tag 0051](https://kerodon.net/tag/0051)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の同型・弱同値の合成・∞ 圏の可逆辺・薄い面と 4 単体を照合。∞ 圏で同型辺が 3-単体上の two-out-of-six を満たす結果。hQCat の圏同値の二取三は扱う射と条件が異なる。

:::

:::proposition "kerodon_5_4_6_6" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1")
Kerodon Proposition 5.4.6.6（[Tag 01XV](https://kerodon.net/tag/01XV)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の同型・弱同値の合成・∞ 圏の可逆辺・薄い面と 4 単体を照合。two-out-of-six と恒等辺の包含から全同型辺を含む結論。通常の RespectsIso は同型辺の包含を別に仮定するか、別種の条件。

:::

:::definition "kerodon_5_4_6_8" (uses := "kerodon_1_1_0_6")
Kerodon Definition 5.4.6.8（[Tag 01XX](https://kerodon.net/tag/01XX)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の同型・弱同値の合成・∞ 圏の可逆辺・薄い面と 4 単体を照合。4-単体の指定した 2-面の四取五による T の述語。射の三取二や群の五補題は面の所属を扱わない。

:::

:::proposition "kerodon_5_4_6_11" (uses := "kerodon_1_4_0_1, kerodon_5_1_1_1, kerodon_5_1_2_4, kerodon_5_1_4_1, kerodon_5_2_2_4, kerodon_5_4_5_14")
Kerodon Proposition 5.4.6.11（[Tag 01Y0](https://kerodon.net/tag/01Y0)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の同型・弱同値の合成・∞ 圏の可逆辺・薄い面と 4 単体を照合。薄い 2-単体の四取五。Mathlib の group\_five\_lemma は完全列上の同型で、4-単体の面を扱わない。

:::

:::proposition "kerodon_5_4_6_14" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_5_4_3_1, kerodon_5_4_4_1, kerodon_5_4_5_7, kerodon_5_4_6_8")
Kerodon Proposition 5.4.6.14（[Tag 01Y3](https://kerodon.net/tag/01Y3)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の同型・弱同値の合成・∞ 圏の可逆辺・薄い面と 4 単体を照合。退化面の包含などの仮定下での T の四取五の判定。退化単体の一般補題は指定面の所属関係を比較しない。

:::

# 5.4.7 Functors of ∞-Bicategories

%%%
number := false
tag := "kerodon-5-4-7"
%%%

Kerodon [Tag 01Y4](https://kerodon.net/tag/01Y4)

:::definition "kerodon_5_4_7_1" (uses := "kerodon_1_1_0_6")
Kerodon Definition 5.4.7.1（[Tag 01Y5](https://kerodon.net/tag/01Y5)）。対応表の状態：なし。

pseudofunctorToPithは通常双圏のpseudofunctorを制限する構成。原文の単体集合の射がthin2単体を保つという述語ではない。

宣言：`CategoryTheory.Bicategory.Pith.pseudofunctorToPith`

:::

:::proposition "kerodon_5_4_7_9" (uses := "kerodon_1_1_0_6, kerodon_5_4_5_10, kerodon_5_4_6_11, kerodon_5_4_6_14")
Kerodon Proposition 5.4.7.9（[Tag 01YC](https://kerodon.net/tag/01YC)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常双圏の関手・∞ 圏と core の比較・左右 slice/coslice の特殊化を照合。薄さ保存を指定退化三角形・任意の辺への条件などで判定する同値。普通の nerve の関手性ではこの述語を特徴づけない。

:::

:::proposition "kerodon_5_4_7_10" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_5_4_2_1, kerodon_5_4_2_6, kerodon_5_4_5_6, kerodon_5_4_7_9")
Kerodon Proposition 5.4.7.10（[Tag 01YD](https://kerodon.net/tag/01YD)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常双圏の関手・∞ 圏と core の比較・左右 slice/coslice の特殊化を照合。interior fibration の薄さ保存と Pith の pullback 四角・誘導射の性質。core の induced map の型は 1-面の可逆性に基づく。

:::

:::corollary "kerodon_5_4_7_11" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_5_1_4_1, kerodon_5_4_5_14, kerodon_5_4_7_10")
Kerodon Corollary 5.4.7.11（[Tag 01YE](https://kerodon.net/tag/01YE)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常双圏の関手・∞ 圏と core の比較・左右 slice/coslice の特殊化を照合。∞-bicategory の slice/coslice 射影を薄い面の延長で判定する結果。通常の slice/coslice の反転同型には薄さがない。

:::

:::corollary "kerodon_5_4_7_12" (uses := "kerodon_1_4_0_1, kerodon_5_1_1_1, kerodon_5_1_4_1, kerodon_5_4_7_11")
Kerodon Corollary 5.4.7.12（[Tag 01YF](https://kerodon.net/tag/01YF)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常双圏の関手・∞ 圏と core の比較・左右 slice/coslice の特殊化を照合。Pith の点上の slice 射影の cartesian 性と Pith(C)\_\{/Z\} の非充満な像。通常の slice の全部分複体の議論とは異なる。

:::

:::corollary "kerodon_5_4_7_14"
Kerodon Corollary 5.4.7.14（[Tag 01YH](https://kerodon.net/tag/01YH)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常双圏の関手・∞ 圏と core の比較・左右 slice/coslice の特殊化を照合。K₀⊂K に沿う slice/coslice の射が ∞-bicategory functor となる薄さ保存。普通の restriction は単体集合射で薄さを指定しない。

:::

# 5.4.8 Strict ∞-Bicategories

%%%
number := false
tag := "kerodon-5-4-8"
%%%

Kerodon [Tag 01YK](https://kerodon.net/tag/01YK)

:::theorem "kerodon_5_4_8_1" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_2_4_5_4, kerodon_2_4_5_5, kerodon_4_4_5_8, kerodon_5_4_8_4, kerodon_5_4_8_5")
Kerodon Theorem 5.4.8.1（[Tag 01YL](https://kerodon.net/tag/01YL)）。対応表の状態：なし。

引用は準圏性まで。原文の∞-bicategoryはthinな2単体の条件と指定退化面を持つ外hornの延長も課し、準圏の内horn充填性の型だけがその全条件を直接返すわけではない。準圏から∞-bicategoryへの比較を欠く。

宣言：`SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialNerve_quasicategory`

:::

:::proposition "kerodon_5_4_8_2" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_2_4_3_1, kerodon_2_4_5_4, kerodon_2_4_5_5, kerodon_2_4_5_8, kerodon_2_4_5_10, kerodon_4_4_5_8")
Kerodon Proposition 5.4.8.2（[Tag 01YM](https://kerodon.net/tag/01YM)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：局所 Kan・hc nerve・2 単体と 1 射の比較・内外ホーンと coreを照合。hc nerve の 2-単体を表す μ:g∘f→h が enriched Hom で可逆なら、その三角形が薄いという主張。2-単体の構成だけでは薄さ判定を持たない。

:::

:::proposition "kerodon_5_4_8_4" (uses := "kerodon_1_1_0_6, kerodon_2_4_4_10, kerodon_2_4_4_16, kerodon_2_4_5_5")
Kerodon Proposition 5.4.8.4（[Tag 01YP](https://kerodon.net/tag/01YP)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：局所 Kan・hc nerve・2 単体と 1 射の比較・内外ホーンと coreを照合。最終ホーンと標準単体の Path の指定 Hom 比較を部分立方体で同定。内ホーンの necklace 分解は最終ホーンの指定 Hom ではない。

:::

:::corollary "kerodon_5_4_8_5" (uses := "kerodon_1_1_0_6, kerodon_2_4_6_13")
Kerodon Corollary 5.4.8.5（[Tag 01YQ](https://kerodon.net/tag/01YQ)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：局所 Kan・hc nerve・2 単体と 1 射の比較・内外ホーンと coreを照合。最後の三角形を同型に送る hc nerve の外ホーンの延長。局所 Kan の hc nerve の ∞ 圏性は内ホーンを扱う。

:::

:::proposition "kerodon_5_4_8_6" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_5_4_7_9, kerodon_5_4_8_1")
Kerodon Proposition 5.4.8.6（[Tag 01YR](https://kerodon.net/tag/01YR)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：局所 Kan・hc nerve・2 単体と 1 射の比較・内外ホーンと coreを照合。locally quasicategory な豊穣関手の hc nerve が薄さを保存する結果。coherentNerveMap は射を作るが薄い 2-単体に関する述語がない。

:::

:::proposition "kerodon_5_4_8_7" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_2_3_2_5, kerodon_5_4_8_2, kerodon_5_4_8_6")
Kerodon Proposition 5.4.8.7（[Tag 01YS](https://kerodon.net/tag/01YS)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：局所 Kan・hc nerve・2 単体と 1 射の比較・内外ホーンと coreを照合。hc nerve の三角形が薄いことと enriched Hom の比較辺 μ が同型であることの同値。局所 Kan の比較では μ の可逆性を特徴づけない。

:::

:::corollary "kerodon_5_4_8_8"
Kerodon Corollary 5.4.8.8（[Tag 01YT](https://kerodon.net/tag/01YT)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：局所 Kan・hc nerve・2 単体と 1 射の比較・内外ホーンと coreを照合。各 enriched Hom の core を取る構成の hc nerve と、元の hc nerve の Pith の厳密同型。coherentNerveCoreIso は可逆な 1-辺で張る core を扱う。

:::

# 5.4.9 Comparison of Homotopy Transport Representations

%%%
number := false
tag := "kerodon-5-4-9"
%%%

Kerodon [Tag 02RX](https://kerodon.net/tag/02RX)

:::proposition "kerodon_5_4_9_1"
Kerodon Proposition 5.4.9.1（[Tag 02RY](https://kerodon.net/tag/02RY)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：局所 Kan の比較・hC の通常圏版・左右 pinchedを照合。locally Kan な C で hC の同型と比較した enriched Hom の π₀ 上の図式。既存の hC と hc nerve の同型に指定された三角形の可換性はない。

:::

:::theorem "kerodon_5_4_9_2" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_2_4_3_1, kerodon_4_6_7_3, kerodon_4_6_7_8, kerodon_5_1_1_1, kerodon_5_1_4_1, kerodon_5_4_4_1, kerodon_5_4_8_7")
Kerodon Theorem 5.4.9.2（[Tag 02RZ](https://kerodon.net/tag/02RZ)）。対応表の状態：なし。

coherentHomIntervalComparisonの同値はinterval写像空間への比較。原文の指定θはleft-pinchedへの射で、さらに豊穣輸送との自然同型を要求する。同じθと自然性への比較が引用型にない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison_isQCatEquivalence`

:::

