module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitConstantTriangle
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitUnitTetrahedronSides
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.TetrahedronFaceDiagramEdges

/-!
概要：元の単位三角柱の二つの内部面を、元の六辺を持つ指定合成三角形へ戻す。
方針：元の実三単体の面をそのまま使い、共有辺と既知の外側面から三辺を回収する。
規約：内部面を充填で選ばない。使われ方：元の三つの単位三単体の境界データ。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {l : SSet.Homotopy F G} {r : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle l r d)
local notation "X" => Functor.obj (ihom (Functor.obj SSet.uliftFunctor B)) SpaceInfinity
local notation "s₀" => coherentColimitUnitTriangleTetrahedron B T 0
local notation "s₂" => coherentColimitUnitTriangleTetrahedron B T 2

/-- 最初と中央の元の三単体の共有面を、元の実三辺で読む。 -/
def coherentColimitUnitInteriorFirst : FunctorCompositionTriangle
    (coherentColimitUnitDiagonal B l)
    (simplicialHomotopyOfFunctorEdge (coherentColimitConstantEdge B r))
    (coherentColimitUnitDiagonal B d) where
  diagram := SSet.yonedaEquiv.symm ((X).δ 1 s₀)
  face_zero := by
    rw [tetrahedronFaceDiagram_edge s₀ 0 0 1 0 (tetrahedronEdge23_eq s₀),
      coherentColimitUnitTriangleTetrahedron_first, Equiv.symm_apply_apply]
    exact (coherentColimitConstantTriangle B T).face_zero
  face_one := by
    rw [tetrahedronFaceDiagram_edge s₀ 1 1 1 2 (tetrahedronEdge03_eq s₀),
      coherentColimitUnitTetrahedron_upper_long, Equiv.symm_apply_apply]
    exact (coherentColimitUnitLowerTriangle B d).face_one
  face_two := by
    rw [tetrahedronFaceDiagram_edge s₀ 2 1 1 3 (tetrahedronEdge02_eq s₀),
      coherentColimitUnitTetrahedron_upper_first, Equiv.symm_apply_apply]
    exact (coherentColimitUnitLowerTriangle B l).face_one

/-- 中央と最後の元の三単体の共有面を、元の実三辺で読む。 -/
def coherentColimitUnitInteriorLast : FunctorCompositionTriangle l
    (coherentColimitUnitDiagonal B r) (coherentColimitUnitDiagonal B d) where
  diagram := SSet.yonedaEquiv.symm ((X).δ 2 s₂)
  face_zero := by
    rw [tetrahedronFaceDiagram_edge s₂ 0 1 2 0 (tetrahedronEdge13_eq s₂),
      coherentColimitUnitTetrahedron_lower_last, Equiv.symm_apply_apply]
    exact (coherentColimitUnitUpperTriangle B r).face_one
  face_one := by
    rw [tetrahedronFaceDiagram_edge s₂ 1 1 2 1 (tetrahedronEdge03_eq s₂).symm,
      coherentColimitUnitTetrahedron_lower_long, Equiv.symm_apply_apply]
    exact (coherentColimitUnitUpperTriangle B d).face_one
  face_two := by
    rw [tetrahedronFaceDiagram_edge s₂ 2 2 2 3 (tetrahedronEdge01_eq s₂).symm,
      coherentColimitUnitTriangleTetrahedron_last, Equiv.symm_apply_apply]
    exact T.face_two

/-- 第一内部面は、元の最初の三単体の同じ面そのもの。 -/
lemma coherentColimitUnitInteriorFirst_face :
    (X).δ 1 s₀ = SSet.yonedaEquiv (coherentColimitUnitInteriorFirst B T).diagram :=
  (Equiv.apply_symm_apply SSet.yonedaEquiv _).symm

/-- 第二内部面は、元の最後の三単体の同じ面そのもの。 -/
lemma coherentColimitUnitInteriorLast_face :
    (X).δ 2 s₂ = SSet.yonedaEquiv (coherentColimitUnitInteriorLast B T).diagram :=
  (Equiv.apply_symm_apply SSet.yonedaEquiv _).symm

end SerrePositivity.InfinityCategories.F2
