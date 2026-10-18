module

public import SerrePositivity.InfinityCategories.F1.PointedSpaceLeftResolution
public import SerrePositivity.InfinityCategories.F1.EdgewiseOppositeKanComparison

/-!
概要：一般の coherent な図式の反転した共通モデルの unstraightening の fiber を左解像で表示する。
方針：共通解像上の値を取り出し、反転した値の普遍 fiber の厳密な模型を適用する。
規約：各 fiber の具体的な比較であり、図式全体の復元の自然性は別に証明する。
使われ方：Kerodon Corollary 5.6.0.6、一般の coherent な図式の復元比較の fiber での座標。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 概要：一般の図式を共通解像へ移したときの頂点の Kan 複体。
方針：持ち上げた図式の coherent な頂点から元の対象を取り出す。
規約：元の F の値との比較は関手同型を介する。
使われ方：Kerodon Corollary 5.6.0.6、左解像の具体的な入力となる共通モデルの値。 -/
noncomputable def edgewiseCoherentDiagramValue {B : SSet.{u + 1}}
    (F : B ⟶ SpaceInfinity.{u}) (b : B _⦋0⦌) : KanObject.{u} :=
  (coherentNerveObject ((edgewiseCoherentDiagramLift F).app (Opposite.op ⦋0⦌) b)).val

/-- 概要：反転した共通モデルの頂点の値は、共通解像で取り出した Kan 複体の反転。
方針：coherent な頂点の復元則と豊穣関手の頂点での公式を使う。
規約：ここでは元の F の値との厳密な等式を主張しない。
使われ方：Kerodon Example 5.6.2.9、普遍 fiber の左解像の同型の適用条件。 -/
lemma edgewiseCoherentOppositeReplacement_vertex {B : SSet.{u + 1}}
    (F : B ⟶ SpaceInfinity.{u}) (b : B _⦋0⦌) :
    (edgewiseCoherentOppositeReplacement F).app (Opposite.op ⦋0⦌) b =
      spaceInfinityVertex (kanObjectOpFunctor.obj (edgewiseCoherentDiagramValue F b)) := by
  change (coherentNerveMap edgewiseOppositeKanEnriched).app (Opposite.op ⦋0⦌)
    ((edgewiseCoherentDiagramLift F).app (Opposite.op ⦋0⦌) b) = _
  rw [← coherentNerveVertex_object ((edgewiseCoherentDiagramLift F).app (Opposite.op ⦋0⦌) b),
    coherentNerveMap_vertex, spaceInfinityVertex_eq_coherent]
  rfl

/-- 概要：反転した共通モデルの unstraightening の各 fiber は共通解像の値の左解像と厳密に同型。
方針：引き戻しの fiber を普遍 fiber へ移し、値の公式と左解像の標準同型を続ける。
規約：底 B の quasicategory 性を仮定しない。
使われ方：Kerodon Corollary 5.6.0.6、一般の coherent な図式の fiber の具体的な表示。 -/
noncomputable def edgewiseOppositeUnstraighteningFiberResolutionIso {B : SSet.{u + 1}}
    (F : B ⟶ SpaceInfinity.{u}) (b : B _⦋0⦌) :
    vertexFiber (leftUnstraighteningProjection (edgewiseCoherentOppositeReplacement F)) b ≅
      (SSet.uliftFunctor.{u + 1, u}).obj (coherentLeftResolution (edgewiseCoherentDiagramValue F b).obj) :=
  leftUnstraighteningFiberIso (edgewiseCoherentOppositeReplacement F) b ≪≫
    eqToIso (congrArg (vertexFiber pointedSpaceProjection) (edgewiseCoherentOppositeReplacement_vertex F b)) ≪≫
      pointedSpaceLeftResolutionIso (edgewiseCoherentDiagramValue F b)

/-- 概要：共通解像の値から一般の coherent な図式の反転モデルの fiber への具体的な比較射。
方針：値の左解像への標準比較を持ち上げ、fiber の厳密な座標同型の逆を続ける。
規約：同値の逆の選択は使わない。
使われ方：Kerodon Corollary 5.6.0.6、復元比較の各 fiber への入力となる実際の射。 -/
noncomputable def edgewiseOppositeUnstraighteningFiberComparison {B : SSet.{u + 1}}
    (F : B ⟶ SpaceInfinity.{u}) (b : B _⦋0⦌) :
    (SSet.uliftFunctor.{u + 1, u}).obj (edgewiseCoherentDiagramValue F b).obj ⟶
      vertexFiber (leftUnstraighteningProjection (edgewiseCoherentOppositeReplacement F)) b :=
  (SSet.uliftFunctor.{u + 1, u}).map
      (coherentLeftResolutionComparison (edgewiseCoherentDiagramValue F b).obj) ≫
    (edgewiseOppositeUnstraighteningFiberResolutionIso F b).inv

/-- 概要：共通解像の値から反転モデルの実際の fiber への比較射は同値。
方針：左解像の標準比較の同値を持ち上げ、厳密な fiber の座標同型を合成する。
規約：各 fiber の射そのものの同値性。
使われ方：Kerodon Corollary 5.6.0.6、一般の coherent な図式の復元比較の fiber での検査。 -/
lemma edgewiseOppositeUnstraighteningFiberComparison_isQCatEquivalence {B : SSet.{u + 1}}
    (F : B ⟶ SpaceInfinity.{u}) (b : B _⦋0⦌) :
    IsQCatEquivalence (edgewiseOppositeUnstraighteningFiberComparison F b) :=
  (coherentLeftResolutionComparison_isQCatEquivalence
    (edgewiseCoherentDiagramValue F b).obj).ulift_of_kan.comp
      (qCatEquivalenceOfIso (edgewiseOppositeUnstraighteningFiberResolutionIso F b).symm).isQCatEquivalence

end SerrePositivity.InfinityCategories
