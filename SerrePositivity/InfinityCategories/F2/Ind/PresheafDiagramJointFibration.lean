module

public import SerrePositivity.InfinityCategories.F2.Ind.UnderSectionRightDiagram
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.SmallLeftUnstraightening
public import SerrePositivity.InfinityCategories.HomotopyLimits.UniverseSSetMaps

/-!
概要：元の coherent 前層図式の共同評価から、同じ積上の小さい left fibration を作る。
方針：元の図式を uncurry し、積の宇宙持ち上げを戻して小さい unstraightening を取る。
規約：任意の coherent 図式を扱う。底の前層変数を切断で消去しない。
使われ方：同じ図式の strict right fibration 表示と大域比較の始点。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {I : Type u} [Category.{u} I] {C : SSet.{u}}
  (F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve I) ⟶ PresheafInfinity C)

/-- 元の全図式の共同評価。全ての高次単体を同じ uncurry で保持する。 -/
def presheafDiagramJointEvaluation :
    (SSet.uliftFunctor.{u + 1, u}).obj (C.op ⊗ nerve I) ⟶ SpaceInfinity.{u} :=
  (HomotopyLimits.uliftTensorIso.{u, u + 1} C.op (nerve I)).hom ≫ uncurry F

/-- 共同評価の小さい unstraightening の、元の積への射影。 -/
def presheafDiagramJointProjection :
    smallLeftUnstraightening (presheafDiagramJointEvaluation F) ⟶ C.op ⊗ nerve I :=
  smallLeftUnstraighteningProjection (presheafDiagramJointEvaluation F)

instance presheafDiagramJointProjection_leftFibration :
    LeftFibration (presheafDiagramJointProjection F) :=
  smallLeftUnstraighteningProjection_leftFibration _

/-- 元の coherent 前層図式から構成した、同じ添字の strict right fibration 図式。 -/
def presheafDiagramRightStrict : I ⥤ RightFibrationObject C :=
  underSectionRightStrictDiagram (presheafDiagramJointProjection F)

/-- 元の共同 unstraightening の、指定添字の値への底上の評価。 -/
def presheafDiagramRightEvaluate (i : I) :
    (presheafDiagramRightStrict F).obj i ⟶
      underSectionRightFiber (presheafDiagramJointProjection F) i :=
  underSectionRightEvaluate (presheafDiagramJointProjection F) i

instance presheafDiagramRightStrict_quasicategory [Quasicategory C] (i : I) :
    Quasicategory ((presheafDiagramRightStrict F).obj i).val.left :=
  underSectionRightDiagram_quasicategory _ i

/-- 同じ評価射の全空間上の同値性。大域の分類比較は別途必要。 -/
lemma presheafDiagramRightEvaluate_isQCatEquivalence [Quasicategory C] (i : I) :
    IsQCatEquivalence (presheafDiagramRightEvaluate F i).left :=
  underSectionRightEvaluate_isQCatEquivalence _ i

end SerrePositivity.InfinityCategories.F2.Ind
