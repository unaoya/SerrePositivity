module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.KanConeDiagramComparisonIsos
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.KanDiagramTriangleConstant
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SpaceTriangleConstantFaces
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.FunctorEqIsoAlgebra

/-!
概要：図式上で定値な Kan 錐円柱の二次の比較を等式からの同型へ簡約する。
方針：元の上下三角形の豊穣辺の定値性を証明して合成する。
規約：指定同型の値を保持。使われ方：元の全空間引き戻し比較の整合式の簡約。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {I : Type u} [SmallCategory I] {F : I ⥤ KanObject.{u}}
  {c d : JoinCone (kanDiagramCoherentNerve F)} (T : SSet.Homotopy c.val d.val)
  (hD : (joinInr _ _ ▷ (Δ[1] : SSet.{u + 1})) ≫ T.h =
    CartesianMonoidalCategory.fst _ (Δ[1] : SSet.{u + 1}) ≫ kanDiagramCoherentNerve F)

include hD

/-- 概要：元の図式上側三角形の同型は等式から来る。
方針：定値な図式制限の二単体。規約：指定値。使われ方：図式比較の簡約。 -/
lemma kanConeDiagramUpperIso_isFunctorEqIso {i j : I} (f : i ⟶ j) :
    IsFunctorEqIso (kanConeDiagramUpperIso T f) := by
  apply isFunctorEqIso_spaceInfinityTriangleIso_of_faces
  exact isConstantCoherentTriangle_kanDiagram_upper F (joinInr _ _) T.h hD _

/-- 概要：元の図式下側三角形の同型は等式から来る。
方針：定値な図式制限の二単体。規約：指定値。使われ方：図式比較の簡約。 -/
lemma kanConeDiagramLowerIso_isFunctorEqIso {i j : I} (f : i ⟶ j) :
    IsFunctorEqIso (kanConeDiagramLowerIso T f) := by
  apply isFunctorEqIso_spaceInfinityTriangleIso_of_faces
  exact isConstantCoherentTriangle_kanDiagram_lower F (joinInr _ _) T.h hD _

/-- 概要：元の図式比較そのものが等式から来る同型。
方針：指定された上下同型の反転と合成。規約：値の同定。使われ方：自然性の簡約。 -/
lemma kanConeDiagramComparisonIso_isFunctorEqIso {i j : I} (f : i ⟶ j) :
    IsFunctorEqIso (kanConeDiagramComparisonIso T f) :=
  (kanConeDiagramLowerIso_isFunctorEqIso T hD f).symm.trans
    (kanConeDiagramUpperIso_isFunctorEqIso T hD f)

end SerrePositivity.InfinityCategories.F2
