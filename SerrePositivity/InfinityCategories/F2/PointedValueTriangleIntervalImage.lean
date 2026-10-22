module

public import SerrePositivity.InfinityCategories.F2.CoherentKanRefinementValueSquare
public import SerrePositivity.InfinityCategories.F2.PointedValueTriangleSquare

/-!
概要：元の精密化の右区間の値は、元の三角形の指定輸送比較そのもの。
方針：実一単体の厳密な一致から同じ類の同型の一致を回収する。
規約：元の精密化と指定輸送を保持。使われ方：左右区間の値の四角形の右辺。
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

/-- 同じ精密化の右区間の値の実辺は、既存の三角形輸送の実辺と一致する。 -/
lemma pointedValueTriangleIntervalImage_edge :
    ((coherentKanRightRefinementEdge (s.obj ⟨ULift.up 0⟩) (s.obj ⟨ULift.up 2⟩)
      (coherentTriangleHomotopy s)).map
      (pointedIntervalValueAction (s.obj ⟨ULift.up 0⟩) (s.obj ⟨ULift.up 2⟩))).edge =
    ((pointedValueTriangleCoefficient s).map
      (pointedValueHomTransport (s.obj ⟨ULift.up 0⟩) (s.obj ⟨ULift.up 2⟩))).edge := by
  change (pointedIntervalValueAction (s.obj ⟨ULift.up 0⟩)
    (s.obj ⟨ULift.up 2⟩)).app (Opposite.op ⦋1⦌)
      ((coherentKanRightHomInterval (s.obj ⟨ULift.up 0⟩) (s.obj ⟨ULift.up 2⟩)).app
        (Opposite.op ⦋1⦌) (ULift.up (coherentTriangleHomotopy s))) =
    (pointedValueHomTransport (s.obj ⟨ULift.up 0⟩) (s.obj ⟨ULift.up 2⟩)).app
      (Opposite.op ⦋1⦌) (ULift.up (coherentTriangleHomotopy s))
  rfl

/-- 右区間の元の類の値は、元の三角形の指定された輸送同型と値まで一致する。 -/
lemma pointedValueTriangleIntervalImage_iso :
    HEq (VertexIso.map
      (coherentKanRightRefinementIso (s.obj ⟨ULift.up 0⟩) (s.obj ⟨ULift.up 2⟩)
        (coherentTriangleHomotopy s))
      (pointedIntervalValueAction (s.obj ⟨ULift.up 0⟩) (s.obj ⟨ULift.up 2⟩)))
      (pointedValueTriangleTransportIso s) := by
  exact vertexIso_heq_of_edge_representatives _ _
    ((coherentKanRightRefinementEdge (s.obj ⟨ULift.up 0⟩) (s.obj ⟨ULift.up 2⟩)
      (coherentTriangleHomotopy s)).map
      (pointedIntervalValueAction (s.obj ⟨ULift.up 0⟩) (s.obj ⟨ULift.up 2⟩)))
    ((pointedValueTriangleCoefficient s).map
      (pointedValueHomTransport (s.obj ⟨ULift.up 0⟩) (s.obj ⟨ULift.up 2⟩)))
    rfl rfl (pointedValueTriangleIntervalImage_edge s)

end SerrePositivity.InfinityCategories.F2
