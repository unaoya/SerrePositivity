module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedHomTriangleEvaluationComparisons
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedHomRefinementTargetMorphism
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedHomMorphismCompositionDisplay

/-!
概要：元の三角形の二辺比較を、元の同じ二射の合成の固定比較へ戻す。
方針：元の精密化の終点と同じ厳密な後合成則で両端を揃える。
規約：元の二段作用と指定比較の値を保持。使われ方：二辺の普遍比較との照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (s : SpaceInfinity.{u} _⦋2⦌)
local notation "f" => coherentEdgeHom (SpaceInfinity.δ 2 s)
local notation "g" => coherentEdgeHom (SpaceInfinity.δ 0 s)

/-- 元の二辺の値比較は、元の同じ二射の合成の固定比較そのもの。 -/
lemma pointedHomTriangleCompositeValueComparison_eq_morphism :
    pointedHomTriangleCompositeValueComparison s =
      pointedHomCompositeMorphismValueComparison f g := by
  have h : (SimplicialCategory.sHom (s.obj ⟨ULift.up 0⟩) (s.obj ⟨ULift.up 2⟩)).δ 0
      (coherentTriangleHomotopy s) = functorVertex (f ≫ g) := by
    rw [coherentTriangleHomotopy_target, kanHom_vertex]
    rfl
  have ht : HEq (pointedHomTriangleCompositeValueComparison s)
      (pointedHomMorphismValueComparison (f ≫ g)) :=
    (vertexIsoOfEq_heq _ _ _).trans
      (pointedHomRefinementTargetValue_heq_morphism (f ≫ g) (coherentTriangleHomotopy s) h)
  have hc : HEq (pointedHomCompositeMorphismValueComparison f g)
      (pointedHomMorphismValueComparison (f ≫ g)) := vertexIsoOfEq_heq _ _ _
  exact eq_of_heq (ht.trans hc.symm)

/-- 同じ二辺での評価比較も、同じ二射の合成の固定比較を保持する。 -/
lemma pointedHomTriangleCompositeEvaluationComparison_eq_morphism :
    pointedHomTriangleCompositeEvaluationComparison s =
      pointedHomCompositeMorphismEvaluationComparison f g := by
  unfold pointedHomTriangleCompositeEvaluationComparison
    pointedHomCompositeMorphismEvaluationComparison
  rw [pointedHomTriangleCompositeValueComparison_eq_morphism]
  rfl

end SerrePositivity.InfinityCategories.F2
