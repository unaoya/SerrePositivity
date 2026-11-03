module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedHomTriangleEvaluationComparisons
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedHomRefinementSourceMorphism

/-!
概要：元の三角形の長辺の全係数比較は、元の同じ長辺の固定比較である。
方針：元の精密化の始点の面を回収し、指定比較の両端の表示だけを除く。
規約：元の指定比較の値を保持。使われ方：長辺の実普遍比較の値との照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の三角形の長辺の値比較は、元の長辺だけで決まる同じ指定比較。 -/
lemma pointedHomTriangleLongValueComparison_eq_morphism (s : SpaceInfinity.{u} _⦋2⦌) :
    pointedHomTriangleLongValueComparison s =
      pointedHomMorphismValueComparison (coherentEdgeHom (SpaceInfinity.δ 1 s)) := by
  have h : (SimplicialCategory.sHom (s.obj ⟨ULift.up 0⟩) (s.obj ⟨ULift.up 2⟩)).δ 1
      (coherentTriangleHomotopy s) =
      functorVertex (coherentEdgeHom (SpaceInfinity.δ 1 s)) := by
    rw [coherentTriangleHomotopy_source, kanHom_vertex]
    rfl
  exact eq_of_heq ((vertexIsoOfEq_heq _ _ _).trans
    (pointedHomRefinementSourceValue_heq_morphism
      (coherentEdgeHom (SpaceInfinity.δ 1 s)) (coherentTriangleHomotopy s) h))

/-- 元の長辺での評価比較も、その同じ長辺だけで決まる指定比較を保持する。 -/
lemma pointedHomTriangleLongEvaluationComparison_eq_morphism
    (s : SpaceInfinity.{u} _⦋2⦌) :
    pointedHomTriangleLongEvaluationComparison s =
      pointedHomMorphismEvaluationComparison (coherentEdgeHom (SpaceInfinity.δ 1 s)) := by
  unfold pointedHomTriangleLongEvaluationComparison pointedHomMorphismEvaluationComparison
  rw [pointedHomTriangleLongValueComparison_eq_morphism]
  rfl

end SerrePositivity.InfinityCategories.F2
