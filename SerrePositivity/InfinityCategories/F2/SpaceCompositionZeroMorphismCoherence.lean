module

public import SerrePositivity.InfinityCategories.F2.SpaceCompositionZeroEvaluationCoherence
public import SerrePositivity.InfinityCategories.F2.PointedHomTriangleLongMorphism
public import SerrePositivity.InfinityCategories.F2.PointedHomTriangleCompositeMorphism

/-!
概要：元の零面の値と元の指定三角形の整合を、元の三射の固定比較で表す。
方針：精密化の両端に依存する比較を同じ元の Kan 射の比較へ厳密に戻す。
規約：元の指定精密化と値を保持。使われ方：元の実普遍比較との固定射での照合。
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
local notation "C" => pointedCoherentFiberComparison K ≫
  eqToHom (congrArg (vertexFiber pointedSpaceProjection)
    (Eq.symm (spaceInfinityVertex_eq_coherent K)))
local notation "V" => eqToHom (congrArg (vertexFiber pointedSpaceProjection)
  (Eq.symm (spaceInfinityVertex_eq_coherent L))) ≫
    QCatEquivalence.hom (pointedSpaceFiberValueEquivalence (spaceInfinityVertex L))
local notation "P" => NatTrans.app (pre C)
  (CategoryTheory.Functor.obj SSet.uliftFunctor (KanObject.obj L))

/-- 元の指定零面と三角形の値は、元の長辺と二射合成の固定比較で整合する。 -/
lemma spaceCompositionZero_morphism_coherence :
    spaceCompositionZeroValueIso s V ≪≫
      pointedHomMorphismEvaluationComparison (coherentEdgeHom (SpaceInfinity.δ 1 s)) ≪≫
      VertexIso.map (((spaceInfinityTriangleIso s).ulift.{u, u + 1}).precomp
        (pointedSpaceFiberValueEquivalence (spaceInfinityVertex K)).hom) P =
    pointedHomCompositeMorphismEvaluationComparison (coherentEdgeHom (SpaceInfinity.δ 2 s))
      (coherentEdgeHom (SpaceInfinity.δ 0 s)) := by
  have h := spaceCompositionZero_evaluation_coherence s
  rw [pointedHomTriangleLongEvaluationComparison_eq_morphism,
    pointedHomTriangleCompositeEvaluationComparison_eq_morphism] at h
  exact h

end SerrePositivity.InfinityCategories.F2
