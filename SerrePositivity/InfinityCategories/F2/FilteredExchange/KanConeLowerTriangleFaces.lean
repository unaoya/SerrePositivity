module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.KanConeDiagramEdges

/-!
概要：全錐円柱の下側三角形の三辺を指定 Kan 射に同定する。
方針：図式成分・対角・元の脚の全一単体の一致。
規約：元の二単体を保持。使われ方：中央・最後の比較三単体の六辺。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {I : Type u} [SmallCategory I] {F G : I ⥤ KanObject.{u}}
  {c : JoinCone (kanDiagramCoherentNerve F)} {d : JoinCone (kanDiagramCoherentNerve G)}
  (T : SSet.Homotopy c.val d.val) (K : KanObject.{u})
  (hc : c.vertex = coherentNerveVertex K)

/-- 概要：最後の辺は元の図式成分。
方針：辺の往復。規約：厳密な式。使われ方：比較三角形の三辺。 -/
lemma kanConeLowerTriangle_zero (i : I) :
    SpaceInfinity.δ 0 (coneHomotopyLowerTriangle T (ULift.up (ComposableArrows.mk₀ i))) =
      (coherentNerveEdge (kanConeDiagramComponent T i)).edge :=
  (coneHomotopyLowerTriangle_zero T _).trans (kanConeDiagramComponent_edge T i).symm

/-- 概要：長辺は元の対角射。
方針：辺の往復。規約：厳密な式。使われ方：比較三角形の三辺。 -/
lemma kanConeLowerTriangle_one (i : I) :
    SpaceInfinity.δ 1 (coneHomotopyLowerTriangle T (ULift.up (ComposableArrows.mk₀ i))) =
      (coherentNerveEdge (kanConeHomotopyDiagonal T K hc i)).edge :=
  (coneHomotopyLowerTriangle_one T _).trans (kanConeHomotopyDiagonal_edge T K hc i).symm

/-- 概要：最初の辺は元の native な脚。
方針：辺の往復。規約：厳密な式。使われ方：比較三角形の三辺。 -/
lemma kanConeLowerTriangle_two (i : I) :
    SpaceInfinity.δ 2 (coneHomotopyLowerTriangle T (ULift.up (ComposableArrows.mk₀ i))) =
      (coherentNerveEdge (kanNativeConeLeg c K hc i)).edge :=
  (coneHomotopyLowerTriangle_two T _).trans (kanNativeConeLeg_edge c K hc i).symm

end SerrePositivity.InfinityCategories.F2
