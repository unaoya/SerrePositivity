module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.KanConeTetrahedra
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.ConeHomotopyTetrahedronLowerSides

/-!
概要：Kan 錐の比較三単体の下側の側面。
方針：指定した錐と円柱の面の厳密な等式を使う。
規約：三角形や辺を新しく選択しない。
使われ方：三つの比較三単体の指定同型の合成関係。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

variable {I : Type u} [SmallCategory I] {F G : I ⥤ KanObject.{u}}
  {c : JoinCone (kanDiagramCoherentNerve F)} {d : JoinCone (kanDiagramCoherentNerve G)}
  (T : SSet.Homotopy c.val d.val)
/-- 概要：比較三単体の側面を対応する指定比較三角形に同定する。
方針：形状の元の射の始点・終点と円柱の側面の式を使う。
規約：二単体の厳密な等式を保持する。
使われ方：指定比較同型を四面の合成則へ代入する。 -/
lemma kanConeTetrahedron_lower_first
    {i j : I} (f : i ⟶ j) :
    SpaceInfinity.δ 3 (kanConeTetrahedron T f 1) =
      coneHomotopyLowerTriangle T
        (ULift.up (ComposableArrows.mk₀ i)) := by
  let J := (SSet.uliftFunctor.{u + 1, u}).obj (nerve I)
  have hk : J.δ 1 (ULift.up (nerve.edgeMk f).edge) = ULift.up (ComposableArrows.mk₀ i) := by
    apply ULift.ext
    exact (nerve.edgeMk f).src_eq
  exact (coneHomotopyTetrahedron_lower_first T _).trans
    (congrArg (coneHomotopyLowerTriangle T) hk)
/-- 概要：比較三単体の側面を対応する指定比較三角形に同定する。
方針：形状の元の射の始点・終点と円柱の側面の式を使う。
規約：二単体の厳密な等式を保持する。
使われ方：指定比較同型を四面の合成則へ代入する。 -/
lemma kanConeTetrahedron_lower_last
    {i j : I} (f : i ⟶ j) :
    SpaceInfinity.δ 0 (kanConeTetrahedron T f 2) =
      homotopyEdgeTriangleLower T.h
        ((joinInr (Δ[0] : SSet.{u + 1})
          ((SSet.uliftFunctor.{u + 1, u}).obj (nerve I))).app
            (Opposite.op ⦋1⦌) (ULift.up (nerve.edgeMk f).edge)) :=
  coneHomotopyTetrahedron_lower_last _ _
/-- 概要：比較三単体の側面を対応する指定比較三角形に同定する。
方針：形状の元の射の始点・終点と円柱の側面の式を使う。
規約：二単体の厳密な等式を保持する。
使われ方：指定比較同型を四面の合成則へ代入する。 -/
lemma kanConeTetrahedron_lower_long
    {i j : I} (f : i ⟶ j) :
    SpaceInfinity.δ 1 (kanConeTetrahedron T f 2) =
      coneHomotopyLowerTriangle T
        (ULift.up (ComposableArrows.mk₀ j)) := by
  let J := (SSet.uliftFunctor.{u + 1, u}).obj (nerve I)
  have hk : J.δ 0 (ULift.up (nerve.edgeMk f).edge) = ULift.up (ComposableArrows.mk₀ j) := by
    apply ULift.ext
    exact (nerve.edgeMk f).tgt_eq
  exact (coneHomotopyTetrahedron_lower_long T _).trans
    (congrArg (coneHomotopyLowerTriangle T) hk)

/-- 概要：中央の三単体の図式側の面は元の上三角形。
方針：円柱の側面。規約：指定二単体。使われ方：中央の合成則。 -/
lemma kanConeTetrahedron_upper_last {i j : I} (f : i ⟶ j) :
    SpaceInfinity.δ 0 (kanConeTetrahedron T f 1) =
      homotopyEdgeTriangleUpper T.h ((joinInr (Δ[0] : SSet.{u + 1})
        ((SSet.uliftFunctor.{u + 1, u}).obj (nerve I))).app
          (Opposite.op ⦋1⦌) (ULift.up (nerve.edgeMk f).edge)) :=
  coneHomotopyTetrahedron_upper_last _ _

end SerrePositivity.InfinityCategories.F2
