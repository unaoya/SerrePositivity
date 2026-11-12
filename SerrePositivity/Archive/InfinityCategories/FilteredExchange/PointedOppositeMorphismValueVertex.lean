module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedOppositeHomActionVertex
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.SpaceTriangleHomotopy

/-!
概要：固定 Kan 射での反転 Hom 作用の実頂点を、同じ関手頂点と値へ戻す。
方針：元の豊穣頂点を関手頂点へ厳密に表示変更する。
規約：元の全係数と値を保持。使われ方：固定射の全値比較の実始点の正規化。
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

/-- 元の関手頂点での全反転 Hom 作用は同じ元の後合成の関手頂点。 -/
lemma pointedOppositeHomAction_functorVertex {K L : KanObject.{u}} (f : K ⟶ L) :
    (pointedOppositeHomAction K L).app (Opposite.op ⦋0⦌)
      (ULift.up (SSet.opObjEquiv.symm (functorVertex f))) =
    functorVertex ((SSet.uliftFunctor.{u + 1, u}).map
      (SSet.opFunctor.map (eHomWhiskerLeft SSet pointKanObject f)) ≫
        pointedCoherentFiberComparison L) := by
  have h := pointedOppositeHomAction_vertex f
  rw [kanHom_vertex] at h
  exact h

/-- 元の固定射の全反転 Hom 作用の値は、同じ後合成と値の関手頂点。 -/
lemma pointedOppositeHomValue_morphism_vertex {K L : KanObject.{u}} (f : K ⟶ L)
    {Z : SSet.{u + 1}}
    (V : vertexFiber pointedSpaceProjection (coherentNerveVertex L) ⟶ Z) :
    (pointedOppositeHomAction K L ≫
      (ihom ((SSet.uliftFunctor.{u + 1, u}).obj
        (SimplicialCategory.sHom pointKanObject K).op)).map V).app (Opposite.op ⦋0⦌)
        (ULift.up (SSet.opObjEquiv.symm (functorVertex f))) =
    functorVertex (((SSet.uliftFunctor.{u + 1, u}).map
      (SSet.opFunctor.map (eHomWhiskerLeft SSet pointKanObject f)) ≫
        pointedCoherentFiberComparison L) ≫ V) := by
  exact congrArg (((ihom ((SSet.uliftFunctor.{u + 1, u}).obj
    (SimplicialCategory.sHom pointKanObject K).op)).map V).app (Opposite.op ⦋0⦌))
      (pointedOppositeHomAction_functorVertex f)

end SerrePositivity.InfinityCategories.F2
