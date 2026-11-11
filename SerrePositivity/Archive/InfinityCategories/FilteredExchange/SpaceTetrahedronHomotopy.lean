module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.SpaceTriangleHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CoherentTetrahedronHom
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.EdgeSquareOfEdgeEquality

/-!
概要：𝒮 の三単体の四面の精密化を元の Kan 射間のホモトピーとして比較する。
方針：同じ豊穣 Hom の元の精密化を uncurry し、可換正方形の辺を同定する。
規約：四つの指定円柱の類を保持。使われ方：全錐比較の二次の整合性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：三単体の指定 path の像を元の Kan 射へ戻す。
方針：豊穣頂点の逆対応。規約：両端は 0 と 3。使われ方：四面の共通の四頂点。 -/
def spaceTetrahedronPathMap (s : SpaceInfinity.{u} _⦋3⦌)
    (P : SimplicialThickening.Path
      (ULift.up (0 : Fin 4) : ULift.{u} (Fin 4)) (ULift.up 3)) :
    s.obj ⟨ULift.up 0⟩ ⟶ s.obj ⟨ULift.up 3⟩ :=
  (SimplicialCategory.homEquiv' _ _).symm
    ((s.map ⟨ULift.up 0⟩ ⟨ULift.up 3⟩).app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ P))

/-- 概要：三単体の元の精密化を Kan 射間の指定円柱にする。
方針：内部 Hom の辺をそのまま uncurry。規約：代表の選択なし。使われ方：合成則。 -/
def spaceTetrahedronHomotopy (s : SpaceInfinity.{u} _⦋3⦌)
    {P Q : SimplicialThickening.Path
      (ULift.up (0 : Fin 4) : ULift.{u} (Fin 4)) (ULift.up 3)} (r : P ⟶ Q) :
    SSet.Homotopy (spaceTetrahedronPathMap s P) (spaceTetrahedronPathMap s Q) :=
  simplicialHomotopyOfFunctorEdge ((coherentTetrahedronHomEdge s r).ofEq
    (by rw [← kanHom_vertex]; exact (Equiv.apply_symm_apply _ _).symm)
    (by rw [← kanHom_vertex]; exact (Equiv.apply_symm_apply _ _).symm)).toTruncated

/-- 概要：指定円柱を辺に戻すと元の精密化の全一単体。
方針：Yoneda と curry の両逆。規約：厳密な式。使われ方：可換正方形の輸送。 -/
lemma spaceTetrahedronHomotopy_edge (s : SpaceInfinity.{u} _⦋3⦌)
    {P Q : SimplicialThickening.Path
      (ULift.up (0 : Fin 4) : ULift.{u} (Fin 4)) (ULift.up 3)} (r : P ⟶ Q) :
    (functorEdgeOfSimplicialHomotopy (spaceTetrahedronHomotopy s r)).edge =
      (coherentTetrahedronHomEdge s r).edge := by
  change SSet.yonedaEquiv (curry (uncurry
    (SSet.yonedaEquiv.symm (coherentTetrahedronHomEdge s r).edge))) = _
  rw [curry_uncurry, Equiv.apply_symm_apply]

/-- 概要：四面の指定円柱の二通りの合成は同じ射のホモトピー類。
方針：元の豊穣正方形を全一単体の一致で輸送する。
規約：同じ内部 Hom の中で四辺を同時に比較。使われ方：指定 path の二次の整合。 -/
lemma spaceTetrahedronHomotopy_square (s : SpaceInfinity.{u} _⦋3⦌) :
    SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (spaceTetrahedronHomotopy s coherentTetrahedronRefine013)) ≫
      SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (spaceTetrahedronHomotopy s coherentTetrahedronRefine013Full)) =
    SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (spaceTetrahedronHomotopy s coherentTetrahedronRefine023)) ≫
      SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (spaceTetrahedronHomotopy s coherentTetrahedronRefine023Full)) := by
  exact homMk_square_of_edge_eq
    (coherentTetrahedronHomEdge s coherentTetrahedronRefine013).toTruncated
    (coherentTetrahedronHomEdge s coherentTetrahedronRefine013Full).toTruncated
    (coherentTetrahedronHomEdge s coherentTetrahedronRefine023).toTruncated
    (coherentTetrahedronHomEdge s coherentTetrahedronRefine023Full).toTruncated
    _ _ _ _ (coherentTetrahedronHom_square s)
    (spaceTetrahedronHomotopy_edge s _).symm (spaceTetrahedronHomotopy_edge s _).symm
    (spaceTetrahedronHomotopy_edge s _).symm (spaceTetrahedronHomotopy_edge s _).symm

end SerrePositivity.InfinityCategories.F2
