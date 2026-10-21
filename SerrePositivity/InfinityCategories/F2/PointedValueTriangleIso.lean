module

public import SerrePositivity.InfinityCategories.F2.PointedValueTriangleNaturality
public import SerrePositivity.InfinityCategories.F2.FunctorIsoUliftRecovery
public import SerrePositivity.InfinityCategories.F2.HomotopyIsoWhiskering

/-!
概要：全 Hom 比較の評価側の精密化辺を、元の指定三角形同型へ厳密に戻す。
方針：全円柱の一致と宇宙下降の忠実性を使い、同じ指定同型を回収する。
規約：元の path 類を保持。使われ方：自然性の正方形の評価側の同定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 全 Hom の評価は、元の Kan 射を値比較に前合成した関手の頂点を厳密に回収。 -/
lemma pointedValueHomEvaluation_vertex {K L : KanObject.{u}} (f : K ⟶ L) :
    (pointedValueHomEvaluation K L).app (Opposite.op ⦋0⦌) (ULift.up (functorVertex f)) =
      functorVertex ((pointedSpaceFiberValueEquivalence (spaceInfinityVertex K)).hom ≫
        (SSet.uliftFunctor.{u + 1, u}).map f) := by
  apply CategoryTheory.Functor.functorHom_ext
  intro n α
  apply ConcreteCategory.hom_ext
  intro a
  rfl

variable (s : SpaceInfinity.{u} _⦋2⦌)

/-- 持ち上げた元の精密化円柱は、元の指定三角形同型の持ち上げそのもの。 -/
lemma spaceInfinityTriangleIso_uliftHomotopy :
    functorIsoOfSimplicialHomotopy
        (uliftSimplicialHomotopy.{u, u + 1} (spaceInfinityTriangleHomotopy s)) =
      (spaceInfinityTriangleIso s).ulift.{u, u + 1} := by
  apply functorIsoDown_injective
  have h : functorIsoOfSimplicialHomotopy (spaceInfinityTriangleHomotopy s) =
      spaceInfinityTriangleIso s := by
    apply Iso.ext
    exact (spaceInfinityTriangleIso_homotopy s).symm
  exact (functorIsoDown_uliftHomotopy (spaceInfinityTriangleHomotopy s)).trans
    (h.trans (functorIsoDown_ulift_iso (spaceInfinityTriangleIso s)).symm)

/-- 同じ精密化辺の評価の両端を、元の Kan 射を使う頂点へ厳密に揃える。 -/
def pointedValueTriangleEvaluationEdge :=
  ((pointedValueTriangleCoefficient s).map
    (pointedValueHomEvaluation (s.obj ⟨ULift.up 0⟩) (s.obj ⟨ULift.up 2⟩))).ofEq
      (pointedValueHomEvaluation_vertex (coherentEdgeHom (SpaceInfinity.δ 1 s)))
      (pointedValueHomEvaluation_vertex (coherentEdgeHom (SpaceInfinity.δ 2 s) ≫
        coherentEdgeHom (SpaceInfinity.δ 0 s)))

/-- 正規化した辺は、元の指定精密化円柱の持ち上げを値比較で制限した辺そのもの。 -/
lemma pointedValueTriangleEvaluationEdge_eq :
    (pointedValueTriangleEvaluationEdge s).toTruncated =
      functorEdgeOfSimplicialHomotopy (functorHomotopyPrecomp
        (uliftSimplicialHomotopy.{u, u + 1} (spaceInfinityTriangleHomotopy s))
        (pointedSpaceFiberValueEquivalence (spaceInfinityVertex (s.obj ⟨ULift.up 0⟩))).hom) := by
  apply SSet.Truncated.Edge.ext
  change (pointedValueHomEvaluation (s.obj ⟨ULift.up 0⟩) (s.obj ⟨ULift.up 2⟩)).app
      (Opposite.op ⦋1⦌) (ULift.up (coherentTriangleHomotopy s)) =
    SSet.yonedaEquiv (curry
      (((pointedSpaceFiberValueEquivalence (spaceInfinityVertex (s.obj ⟨ULift.up 0⟩))).hom ▷
        (Δ[1] : SSet.{u + 1})) ≫
          (uliftSimplicialHomotopy.{u, u + 1} (spaceInfinityTriangleHomotopy s)).h))
  apply CategoryTheory.Functor.functorHom_ext
  intro d α
  apply ConcreteCategory.hom_ext
  intro a
  rfl

/-- 評価側の元の辺の類は、指定三角形同型を持ち上げて前合成した同型の順方向。 -/
lemma pointedValueTriangleEvaluationEdge_hom :
    SSet.Truncated.HomotopyCategory.homMk (pointedValueTriangleEvaluationEdge s).toTruncated =
      (((spaceInfinityTriangleIso s).ulift.{u, u + 1}).precomp
        (pointedSpaceFiberValueEquivalence
          (spaceInfinityVertex (s.obj ⟨ULift.up 0⟩))).hom).hom := by
  rw [pointedValueTriangleEvaluationEdge_eq]
  have h := congrArg Iso.hom (homotopyIso_precomp
    (uliftSimplicialHomotopy.{u, u + 1} (spaceInfinityTriangleHomotopy s))
    (pointedSpaceFiberValueEquivalence (spaceInfinityVertex (s.obj ⟨ULift.up 0⟩))).hom)
  rw [spaceInfinityTriangleIso_uliftHomotopy] at h
  exact h

end SerrePositivity.InfinityCategories.F2
