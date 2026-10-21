module

public import SerrePositivity.InfinityCategories.F2.CoherentColimitUnitTetrahedra
public import SerrePositivity.InfinityCategories.F2.CoherentColimitUnitPrismSides

/-!
概要：三つの単位三単体の六側面を、元の三辺の上下単位三角形へ厳密に同定する。
方針：同じ全三角柱の側面公式と、元の正方形からの二単体の一致を合成する。
規約：同型の類だけでなく全二単体を保持。使われ方：指定比較の三つの合成関係。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {l : SSet.Homotopy F G} {r : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle l r d)

/-- 最初の三単体の長辺側面は、元の対角辺の下単位三角形。 -/
lemma coherentColimitUnitTetrahedron_upper_long :
    ((ihom ((SSet.uliftFunctor.{u + 1, u}).obj B)).obj SpaceInfinity.{u}).δ 2
      (coherentColimitUnitTriangleTetrahedron B T 0) =
      SSet.yonedaEquiv (coherentColimitUnitLowerTriangle B d).diagram :=
  (triangleHomotopyTetrahedron_upper_long _ _).trans
    (coherentColimitUnitTrianglePrism_upper B T 1 d T.face_one)

/-- 最初の三単体の短辺側面は、元の最初の辺の下単位三角形。 -/
lemma coherentColimitUnitTetrahedron_upper_first :
    ((ihom ((SSet.uliftFunctor.{u + 1, u}).obj B)).obj SpaceInfinity.{u}).δ 3
      (coherentColimitUnitTriangleTetrahedron B T 0) =
      SSet.yonedaEquiv (coherentColimitUnitLowerTriangle B l).diagram :=
  (triangleHomotopyTetrahedron_upper_first _ _).trans
    (coherentColimitUnitTrianglePrism_upper B T 2 l T.face_two)

/-- 中央の三単体の終端側面は、元の最後の辺の下単位三角形。 -/
lemma coherentColimitUnitTetrahedron_upper_last :
    ((ihom ((SSet.uliftFunctor.{u + 1, u}).obj B)).obj SpaceInfinity.{u}).δ 0
      (coherentColimitUnitTriangleTetrahedron B T 1) =
      SSet.yonedaEquiv (coherentColimitUnitLowerTriangle B r).diagram :=
  (triangleHomotopyTetrahedron_upper_last _ _).trans
    (coherentColimitUnitTrianglePrism_upper B T 0 r T.face_zero)

/-- 中央の三単体の始端側面は、元の最初の辺の上単位三角形。 -/
lemma coherentColimitUnitTetrahedron_lower_first :
    ((ihom ((SSet.uliftFunctor.{u + 1, u}).obj B)).obj SpaceInfinity.{u}).δ 3
      (coherentColimitUnitTriangleTetrahedron B T 1) =
      SSet.yonedaEquiv (coherentColimitUnitUpperTriangle B l).diagram :=
  (triangleHomotopyTetrahedron_lower_first _ _).trans
    (coherentColimitUnitTrianglePrism_lower B T 2 l T.face_two)

/-- 最後の三単体の終端側面は、元の最後の辺の上単位三角形。 -/
lemma coherentColimitUnitTetrahedron_lower_last :
    ((ihom ((SSet.uliftFunctor.{u + 1, u}).obj B)).obj SpaceInfinity.{u}).δ 0
      (coherentColimitUnitTriangleTetrahedron B T 2) =
      SSet.yonedaEquiv (coherentColimitUnitUpperTriangle B r).diagram :=
  (triangleHomotopyTetrahedron_lower_last _ _).trans
    (coherentColimitUnitTrianglePrism_lower B T 0 r T.face_zero)

/-- 最後の三単体の長辺側面は、元の共有対角辺の上単位三角形。 -/
lemma coherentColimitUnitTetrahedron_lower_long :
    ((ihom ((SSet.uliftFunctor.{u + 1, u}).obj B)).obj SpaceInfinity.{u}).δ 1
      (coherentColimitUnitTriangleTetrahedron B T 2) =
      SSet.yonedaEquiv (coherentColimitUnitUpperTriangle B d).diagram :=
  (triangleHomotopyTetrahedron_lower_long _ _).trans
    (coherentColimitUnitTrianglePrism_lower B T 1 d T.face_one)

end SerrePositivity.InfinityCategories.F2
