module

public import SerrePositivity.InfinityCategories.F2.Ind.UnderSectionEvaluation
public import SerrePositivity.InfinityCategories.F2.Ind.StrictRightFibrationOpposite
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafRestrictionEquivalence

/-!
概要：パラメータ付き under 切断を反転し、元の底上の strict right fibration 図式にする。
方針：二重反転の底を標準同型で戻し、同じ底上の評価も反転する。
規約：元の添字と評価射を保持する。大域分類比較は別に構成する。
使われ方：一般 coherent 前層図式の strict 化。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 反対底の通常の left fibration 図式を元の底の right fibration 図式へ戻す。 -/
def leftFibrationOppositeRightOrdinary (B : SSet.{u}) :
    LeftFibrationObject B.op ⥤ RightFibrationObject B where
  obj := leftFibrationOppositeRightObject
  map f := Over.homMk (SSet.opFunctor.map f.left) (by
    change SSet.opFunctor.map f.left ≫ (SSet.opFunctor.map _ ≫ _) =
      SSet.opFunctor.map _ ≫ _
    rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, Over.w])
  map_id p := by
    apply Over.OverMorphism.ext
    exact SSet.opFunctor.map_id p.val.left
  map_comp f g := by
    apply Over.OverMorphism.ext
    exact SSet.opFunctor.map_comp f.left g.left

variable {I : Type u} [Category.{u} I] {B E : SSet.{u}}
  (p : E ⟶ B.op ⊗ nerve I) [LeftFibration p]

/-- 元の底上の、同じ under 切断からなる strict right fibration 図式。 -/
def underSectionRightStrictDiagram : I ⥤ RightFibrationObject B :=
  underSectionStrictDiagram p ⋙ leftFibrationOppositeRightOrdinary B

/-- 元の同じ添字での値を反転した right fibration。 -/
def underSectionRightFiber (i : I) : RightFibrationObject B :=
  leftFibrationOppositeRightObject
    ⟨Over.mk (pullback.snd p (underSectionFiberBase B.op i)),
      underSectionFiberProjection_leftFibration p i⟩

/-- 同じ底上の評価を反転した、指定した元の値への射。 -/
def underSectionRightEvaluate (i : I) :
    (underSectionRightStrictDiagram p).obj i ⟶ underSectionRightFiber p i :=
  (leftFibrationOppositeRightOrdinary B).map
    (Over.homMk (underSectionEvaluate p i) (underSectionEvaluate_projection p i))

instance underSectionRightDiagram_quasicategory [Quasicategory B] (i : I) :
    Quasicategory ((underSectionRightStrictDiagram p).obj i).val.left :=
  inferInstanceAs (Quasicategory (underSectionFamily p i).op)

instance underSectionRightFiber_quasicategory [Quasicategory B] (i : I) :
    Quasicategory (underSectionRightFiber p i).val.left :=
  inferInstanceAs (Quasicategory (pullback p (underSectionFiberBase B.op i)).op)

/-- 反転しても元の評価射自体が全空間の同値を誘導する。 -/
lemma underSectionRightEvaluate_isQCatEquivalence [Quasicategory B] (i : I) :
    IsQCatEquivalence (underSectionRightEvaluate p i).left :=
  (underSectionEvaluate_isQCatEquivalence p i).opposite

end SerrePositivity.InfinityCategories.F2.Ind
