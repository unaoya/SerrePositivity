module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.RoofSliceTetrahedronFaces
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FiberCofiber.DiagramTriangleConeBoundary

/-! # 実 over の三次境界が指定する元の四次最後外ホーン

概要：共通辺上で一致する四つの実 over 二単体を、元の四次ホーンの四面へ移す。
方針：回収四面体の三面公式で六つの共通三角形の一致を証明する。
規約：充填の存在は未仮定。使われ方：実図式二単体に沿う辺錐の高次整合性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet
open scoped _root_.Simplicial
variable {X : SSet.{u}} (a : Δ[0] ⟶ X)
variable (B : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ThreeSimplexFaceBoundary (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver a))

/-- 最後の面を除く四面は、指定 over 境界の四つの回収四面体。 -/
def roofPointSliceFourHornFace (i : Fin 5) (hi : i ≠ 4) : Δ[3] ⟶ X :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTetrahedron a (B.face (i.castPred hi))

/-- 六つの実 over 辺の一致は、回収四面体の六つの共通三角形の一致を与える。 -/
lemma roofPointSliceFourHorn_compatible :
    horn.IsCompatible (roofPointSliceFourHornFace a B) := by
  rw [horn.isCompatible_iff]
  intro i j hi hj hij
  fin_cases i <;> fin_cases j
  all_goals try exact (hi rfl).elim
  all_goals try exact (hj rfl).elim
  all_goals try exact False.elim ((by decide : ¬ ((0 : Fin 5) < 0)) hij)
  all_goals try exact False.elim ((by decide : ¬ ((1 : Fin 5) < 0)) hij)
  all_goals try exact False.elim ((by decide : ¬ ((1 : Fin 5) < 1)) hij)
  all_goals try exact False.elim ((by decide : ¬ ((2 : Fin 5) < 0)) hij)
  all_goals try exact False.elim ((by decide : ¬ ((2 : Fin 5) < 1)) hij)
  all_goals try exact False.elim ((by decide : ¬ ((2 : Fin 5) < 2)) hij)
  all_goals try exact False.elim ((by decide : ¬ ((3 : Fin 5) < 0)) hij)
  all_goals try exact False.elim ((by decide : ¬ ((3 : Fin 5) < 1)) hij)
  all_goals try exact False.elim ((by decide : ¬ ((3 : Fin 5) < 2)) hij)
  all_goals try exact False.elim ((by decide : ¬ ((3 : Fin 5) < 3)) hij)
  · change SSet.stdSimplex.δ 0 ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTetrahedron a (B.face 0) =
      SSet.stdSimplex.δ 0 ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTetrahedron a (B.face 1)
    exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTetrahedron_face a (B.face 0) 0).trans
      ((congrArg (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTriangle a) B.h01).trans
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTetrahedron_face a (B.face 1) 0).symm)
  · change SSet.stdSimplex.δ 1 ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTetrahedron a (B.face 0) =
      SSet.stdSimplex.δ 0 ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTetrahedron a (B.face 2)
    exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTetrahedron_face a (B.face 0) 1).trans
      ((congrArg (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTriangle a) B.h02).trans
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTetrahedron_face a (B.face 2) 0).symm)
  · change SSet.stdSimplex.δ 2 ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTetrahedron a (B.face 0) =
      SSet.stdSimplex.δ 0 ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTetrahedron a (B.face 3)
    exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTetrahedron_face a (B.face 0) 2).trans
      ((congrArg (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTriangle a) B.h03).trans
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTetrahedron_face a (B.face 3) 0).symm)
  · change SSet.stdSimplex.δ 1 ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTetrahedron a (B.face 1) =
      SSet.stdSimplex.δ 1 ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTetrahedron a (B.face 2)
    exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTetrahedron_face a (B.face 1) 1).trans
      ((congrArg (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTriangle a) B.h12).trans
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTetrahedron_face a (B.face 2) 1).symm)
  · change SSet.stdSimplex.δ 2 ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTetrahedron a (B.face 1) =
      SSet.stdSimplex.δ 1 ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTetrahedron a (B.face 3)
    exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTetrahedron_face a (B.face 1) 2).trans
      ((congrArg (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTriangle a) B.h13).trans
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTetrahedron_face a (B.face 3) 1).symm)
  · change SSet.stdSimplex.δ 2 ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTetrahedron a (B.face 2) =
      SSet.stdSimplex.δ 2 ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTetrahedron a (B.face 3)
    exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTetrahedron_face a (B.face 2) 2).trans
      ((congrArg (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTriangle a) B.h23).trans
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTetrahedron_face a (B.face 3) 2).symm)

/-- 元の四つの over 二単体を面として指定する、元の単体集合の四次最後外ホーン。 -/
def roofPointSliceFourHorn : (Λ[4, 4] : SSet.{u}) ⟶ X :=
  (roofPointSliceFourHorn_compatible a B).desc

/-- 四次ホーンの各指定面は、元の指定 over 二単体の回収四面体そのもの。 -/
lemma roofPointSliceFourHorn_face (i : Fin 4) :
    horn.ι (4 : Fin 5) i.castSucc (Fin.castSucc_ne_last _) ≫ roofPointSliceFourHorn a B =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTetrahedron a (B.face i) := by
  simpa only [roofPointSliceFourHorn, roofPointSliceFourHornFace,
    Fin.castPred_castSucc] using
    horn.IsCompatible.ι_desc (roofPointSliceFourHorn_compatible a B)
      i.castSucc (Fin.castSucc_ne_last _)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
