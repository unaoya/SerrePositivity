module

public import SerrePositivity.InfinityCategories.F2.KanConeHomotopyDiagonal
public import SerrePositivity.InfinityCategories.F2.ConeHomotopyLowerTriangle
public import SerrePositivity.InfinityCategories.F2.ConeHomotopyUpperTriangle
public import SerrePositivity.InfinityCategories.F2.SpaceTriangleFaces

/-!
概要：Kan 図式上の全錐比較の上下の指定三角形を実際のホモトピーにする。
方針：元の三辺の厳密な同定と精密化の uncurry。
規約：両方で同じ対角射を使う。使われ方：各脚の指定比較と二次の整合性。
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
  (T : SSet.Homotopy c.val d.val) (K L : KanObject.{u})
  (hc : c.vertex = coherentNerveVertex K) (hd : d.vertex = coherentNerveVertex L)

/-- 概要：下側の指定三角形は対角と元の脚・図式成分の合成のホモトピー。
方針：全錐円柱の元の二単体を読み戻す。
規約：元の三角形を保持。使われ方：各脚の指定比較の始域側。 -/
def kanConeHomotopyLower (i : I) (r : F.obj i ⟶ G.obj i)
    (hr : (coneHomotopyDiagramEdge T (ULift.up (ComposableArrows.mk₀ i))).edge =
      (coherentNerveEdge r).edge) :
    SSet.Homotopy (kanConeHomotopyDiagonal T K hc i) (kanNativeConeLeg c K hc i ≫ r) :=
  spaceInfinityTriangleHomotopy_of_faces _ _ _
    (coneHomotopyLowerTriangle T (ULift.up (ComposableArrows.mk₀ i)))
    ((coneHomotopyLowerTriangle_two T _).trans (kanNativeConeLeg_edge c K hc i).symm)
    ((coneHomotopyLowerTriangle_zero T _).trans hr)
    ((coneHomotopyLowerTriangle_one T _).trans (kanConeHomotopyDiagonal_edge T K hc i).symm)

/-- 概要：上側の指定三角形は対角と頂点比較・比較先の脚の合成のホモトピー。
方針：全錐円柱の元の二単体を読み戻す。
規約：下側と同じ対角射。使われ方：各脚の指定比較の終域側。 -/
def kanConeHomotopyUpper (i : I) (a : K ⟶ L)
    (ha : (coneHomotopyApexEdge T).edge = (coherentNerveEdge a).edge) :
    SSet.Homotopy (kanConeHomotopyDiagonal T K hc i) (a ≫ kanNativeConeLeg d L hd i) :=
  spaceInfinityTriangleHomotopy_of_faces _ _ _
    (coneHomotopyUpperTriangle T (ULift.up (ComposableArrows.mk₀ i)))
    ((coneHomotopyUpperTriangle_two T _).trans ha)
    ((coneHomotopyUpperTriangle_zero T _).trans (kanNativeConeLeg_edge d L hd i).symm)
    ((coneHomotopyUpperTriangle_one T _).trans (kanConeHomotopyDiagonal_edge T K hc i).symm)

end SerrePositivity.InfinityCategories.F2
