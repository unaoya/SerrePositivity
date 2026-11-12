module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedValueHomAction
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SpaceTriangleIso
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.InvertibleEdge
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Homotopy
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningSectionNaturality

/-!
概要：元の coherent 三角形の指定精密化辺に対する値比較の自然性。
方針：全 Hom 上の同じ指定比較の自然性を、元の一単体へ適用する。
規約：元の精密化の全円柱を保持。使われ方：二脚の比較と指定 path の整合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (s : SpaceInfinity.{u} _⦋2⦌)

/-- 元の精密化の辺を全体のまま大きい宇宙へ持ち上げた指定辺。 -/
def pointedValueTriangleCoefficient :
    ((SSet.uliftFunctor.{u + 1, u}).obj
      (SimplicialCategory.sHom (s.obj ⟨ULift.up 0⟩) (s.obj ⟨ULift.up 2⟩))).Edge
      (ULift.up (functorVertex (coherentEdgeHom (SpaceInfinity.δ 1 s))))
      (ULift.up (functorVertex (coherentEdgeHom (SpaceInfinity.δ 2 s) ≫
        coherentEdgeHom (SpaceInfinity.δ 0 s)))) :=
  SSet.Edge.ofTruncated (uliftTruncatedEdge.{u, u + 1}
    (spaceInfinityTriangleEdge s).toTruncated)

/-- 元の精密化の評価は、元の指定ホモトピーの持ち上げを値比較で制限した全円柱。 -/
lemma pointedValueTriangleEvaluationDiagram :
    SSet.yonedaEquiv.symm (ULift.up (coherentTriangleHomotopy s)) ≫
        pointedValueHomEvaluation (s.obj ⟨ULift.up 0⟩) (s.obj ⟨ULift.up 2⟩) =
      curry (((pointedSpaceFiberValueEquivalence (spaceInfinityVertex (s.obj ⟨ULift.up 0⟩))).hom ▷
        (Δ[1] : SSet.{u + 1})) ≫
          (uliftSimplicialHomotopy.{u, u + 1} (spaceInfinityTriangleHomotopy s)).h) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro t
  apply CategoryTheory.Functor.functorHom_ext
  intro d α
  apply ConcreteCategory.hom_ext
  intro a
  rfl

/-- 同じ元の精密化辺に対し、両端の指定比較と全区間の輸送の path は可換する。 -/
lemma pointedValueTriangle_naturality :
    SSet.Truncated.HomotopyCategory.homMk
        (((pointedValueTriangleCoefficient s).map
          (pointedValueHomEvaluation (s.obj ⟨ULift.up 0⟩) (s.obj ⟨ULift.up 2⟩))).toTruncated) ≫
      ((pointedValueHomActionIso (s.obj ⟨ULift.up 0⟩) (s.obj ⟨ULift.up 2⟩)).app
        (ULift.up (functorVertex (coherentEdgeHom (SpaceInfinity.δ 2 s) ≫
          coherentEdgeHom (SpaceInfinity.δ 0 s))))).hom =
    ((pointedValueHomActionIso (s.obj ⟨ULift.up 0⟩) (s.obj ⟨ULift.up 2⟩)).app
        (ULift.up (functorVertex (coherentEdgeHom (SpaceInfinity.δ 1 s))))).hom ≫
      SSet.Truncated.HomotopyCategory.homMk
        (((pointedValueTriangleCoefficient s).map
          (pointedValueHomTransport (s.obj ⟨ULift.up 0⟩) (s.obj ⟨ULift.up 2⟩))).toTruncated) := by
  exact functorIso_app_edge_naturality
    (pointedValueHomActionIso (s.obj ⟨ULift.up 0⟩) (s.obj ⟨ULift.up 2⟩))
    (pointedValueTriangleCoefficient s)

end SerrePositivity.InfinityCategories.F2
