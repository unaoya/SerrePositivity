module

public import SerrePositivity.InfinityCategories.F2.PointedOppositeRefinementValue

/-!
概要：反転精密化の値の実両端を、元の二段作用と長辺作用の値へ正規化する。
方針：元の三角形の両面から得た頂点等式に、同じ内部 Hom の値写像を適用する。
規約：元の全係数と値を保持。使われ方：値の整合式の端点の表示変更。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable (s : SpaceInfinity.{u} _⦋2⦌)
local notation "K" => EnrichedFunctor.obj s (SimplicialThickening.mk (ULift.up 0))
local notation "L" => EnrichedFunctor.obj s (SimplicialThickening.mk (ULift.up 2))
local notation "A" => spaceSimplexPointedCoefficients s
local notation "P" => CategoryTheory.Functor.map SSet.uliftFunctor
  (CategoryTheory.Functor.map SSet.opFunctor (eHomWhiskerLeft SSet pointKanObject
    (coherentEdgeHom (SpaceInfinity.δ 2 s))))
local notation "Q" => CategoryTheory.Functor.map SSet.uliftFunctor
  (CategoryTheory.Functor.map SSet.opFunctor (eHomWhiskerLeft SSet pointKanObject
    (coherentEdgeHom (SpaceInfinity.δ 0 s))))
local notation "R" => CategoryTheory.Functor.map SSet.uliftFunctor
  (CategoryTheory.Functor.map SSet.opFunctor (eHomWhiskerLeft SSet pointKanObject
    (coherentEdgeHom (SpaceInfinity.δ 1 s))))

/-- 同じ反転精密化の作用の値の実始点は、元の二段作用の値の頂点。 -/
lemma pointedOppositeRefinementValue_source_vertex {Z : SSet.{u + 1}}
    (V : vertexFiber pointedSpaceProjection (coherentNerveVertex L) ⟶ Z) :
    (pointedOppositeHomAction K L ≫ (ihom A).map V).app (Opposite.op ⦋0⦌)
      (ULift.up (SSet.opObjEquiv.symm
        ((SimplicialCategory.sHom K L).δ 0 (coherentTriangleHomotopy s)))) =
      functorVertex (((P ≫ Q) ≫ pointedCoherentFiberComparison L) ≫ V) := by
  exact congrArg (((ihom A).map V).app (Opposite.op ⦋0⦌))
    ((pointedOppositeRefinementAction_source_eq_triangle s).trans
      (pointedOppositeTriangleAction_source_vertex s))

/-- 同じ反転精密化の作用の値の実終点は、元の長辺作用の値の頂点。 -/
lemma pointedOppositeRefinementValue_target_vertex {Z : SSet.{u + 1}}
    (V : vertexFiber pointedSpaceProjection (coherentNerveVertex L) ⟶ Z) :
    (pointedOppositeHomAction K L ≫ (ihom A).map V).app (Opposite.op ⦋0⦌)
      (ULift.up (SSet.opObjEquiv.symm
        ((SimplicialCategory.sHom K L).δ 1 (coherentTriangleHomotopy s)))) =
      functorVertex ((R ≫ pointedCoherentFiberComparison L) ≫ V) := by
  exact congrArg (((ihom A).map V).app (Opposite.op ⦋0⦌))
    ((pointedOppositeRefinementAction_target_eq_triangle s).trans
      (pointedOppositeTriangleAction_target_vertex s))

end SerrePositivity.InfinityCategories.F2
