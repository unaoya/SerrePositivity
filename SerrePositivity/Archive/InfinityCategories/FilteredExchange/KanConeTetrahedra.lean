module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.KanNativeConeTriangle
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanConeHomotopyTriangles
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.ConeHomotopyTetrahedronUpperSides
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.ConeHomotopyTetrahedronLowerSides

/-!
概要：Kan 図式上の全錐円柱の三つの三単体とその指定面。
方針：形状の元の射に沿う標準 prism の分割。
規約：新しい充填は選ばない。使われ方：指定比較の三つの合成則。
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
  (T : SSet.Homotopy c.val d.val)

/-- 概要：全錐円柱の元の三つの三単体。
方針：標準分割。規約：元の射を保持。使われ方：四面の合成則の入力。 -/
def kanConeTetrahedron {i j : I} (f : i ⟶ j) (r : Fin 3) : SpaceInfinity.{u} _⦋3⦌ :=
  coneHomotopyTetrahedron T (ULift.up (nerve.edgeMk f).edge) r

/-- 概要：最初の三単体の上面は比較先の錐の元の三角形。
方針：円柱の終端。規約：指定二単体。使われ方：第一合成則の上辺。 -/
lemma kanConeTetrahedron_first {i j : I} (f : i ⟶ j) :
    SpaceInfinity.δ 0 (kanConeTetrahedron T f 0) = kanNativeConeTriangle d f :=
  coneHomotopyTetrahedron_first T _

/-- 概要：最後の三単体の下面は元の錐の指定三角形。
方針：円柱の始端。規約：指定二単体。使われ方：第三合成則の下辺。 -/
lemma kanConeTetrahedron_last {i j : I} (f : i ⟶ j) :
    SpaceInfinity.δ 3 (kanConeTetrahedron T f 2) = kanNativeConeTriangle c f :=
  coneHomotopyTetrahedron_last T _

/-- 概要：最初と中央の三単体は元の同じ共有面を持つ。
方針：標準分割の面。規約：厳密な式。使われ方：内部同型の消去。 -/
lemma kanConeTetrahedron_glue_first {i j : I} (f : i ⟶ j) :
    SpaceInfinity.δ 1 (kanConeTetrahedron T f 0) =
      SpaceInfinity.δ 1 (kanConeTetrahedron T f 1) :=
  coneHomotopyTetrahedron_glue_first T _

/-- 概要：中央と最後の三単体は元の同じ共有面を持つ。
方針：標準分割の面。規約：厳密な式。使われ方：内部同型の消去。 -/
lemma kanConeTetrahedron_glue_last {i j : I} (f : i ⟶ j) :
    SpaceInfinity.δ 2 (kanConeTetrahedron T f 1) =
      SpaceInfinity.δ 2 (kanConeTetrahedron T f 2) :=
  coneHomotopyTetrahedron_glue_last T _

/-- 概要：最初の三単体の長い側面は終域への指定上三角形。
方針：元の射の終点。規約：二単体そのもの。使われ方：第一合成則の左辺。 -/
lemma kanConeTetrahedron_upper_long {i j : I} (f : i ⟶ j) :
    SpaceInfinity.δ 2 (kanConeTetrahedron T f 0) =
      coneHomotopyUpperTriangle T (ULift.up (ComposableArrows.mk₀ j)) := by
  have hk : ((SSet.uliftFunctor.{u + 1, u}).obj (nerve I)).δ 0
      (ULift.up (nerve.edgeMk f).edge) = ULift.up (ComposableArrows.mk₀ j) := by
    apply ULift.ext
    exact (nerve.edgeMk f).tgt_eq
  exact (coneHomotopyTetrahedron_upper_long T _).trans
    (congrArg (coneHomotopyUpperTriangle T) hk)

/-- 概要：最初の三単体の短い側面は始域への指定上三角形。
方針：元の射の始点。規約：二単体そのもの。使われ方：第一合成則の右辺。 -/
lemma kanConeTetrahedron_upper_first {i j : I} (f : i ⟶ j) :
    SpaceInfinity.δ 3 (kanConeTetrahedron T f 0) =
      coneHomotopyUpperTriangle T (ULift.up (ComposableArrows.mk₀ i)) := by
  have hk : ((SSet.uliftFunctor.{u + 1, u}).obj (nerve I)).δ 1
      (ULift.up (nerve.edgeMk f).edge) = ULift.up (ComposableArrows.mk₀ i) := by
    apply ULift.ext
    exact (nerve.edgeMk f).src_eq
  exact (coneHomotopyTetrahedron_upper_first T _).trans
    (congrArg (coneHomotopyUpperTriangle T) hk)

end SerrePositivity.InfinityCategories.F2
