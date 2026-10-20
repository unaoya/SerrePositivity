module
public import SerrePositivity.KST.SConstruction.TriangleBoundaryCylinder

/-! # 元の三辺円柱を全境界ホモトピーとして回収
概要：貼った境界円柱の両端と各側面を、入力した元の全辺として厳密に回収する。
方針：境界の各面で両端を照合し、元の全三角形の境界との等号も与える。
規約：元の実円柱を保持し、三角形の選び直しや充填は行わない。
使われ方：指定三辺への相対三角形移送に渡す実境界ホモトピー。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
variable {E : SSet.{u}} {x y z : E _⦋0⦌}
  {f₀ f₁ : E.Edge x y} {g₀ g₁ : E.Edge y z} {h₀ h₁ : E.Edge x z}
  (Hf : EndpointFixedEdgeCylinder f₀ f₁) (Hg : EndpointFixedEdgeCylinder g₀ g₁)
  (Hh : EndpointFixedEdgeCylinder h₀ h₁)

/-- 入力した三つの全辺円柱を両端と側面に持つ、同じ全境界ホモトピー。 -/
def triangleBoundaryHomotopy :
    Homotopy (triangleBoundaryMap f₀ g₀ h₀) (triangleBoundaryMap f₁ g₁ h₁) where
  h := triangleBoundaryCylinderMap Hf Hg Hh
  h₀ := by
    change SSet.ι₀ ≫ triangleBoundaryCylinderMap Hf Hg Hh = triangleBoundaryMap f₀ g₀ h₀
    apply SSet.boundary.hom_ext
    intro i
    rw [← SSet.ι₀_comp_assoc, triangleBoundaryCylinderMap_face, triangleBoundaryMap_face]
    fin_cases i
    · exact Hg.homotopy.h₀
    · exact Hh.homotopy.h₀
    · exact Hf.homotopy.h₀
  h₁ := by
    change SSet.ι₁ ≫ triangleBoundaryCylinderMap Hf Hg Hh = triangleBoundaryMap f₁ g₁ h₁
    apply SSet.boundary.hom_ext
    intro i
    rw [← SSet.ι₁_comp_assoc, triangleBoundaryCylinderMap_face, triangleBoundaryMap_face]
    fin_cases i
    · exact Hg.homotopy.h₁
    · exact Hh.homotopy.h₁
    · exact Hf.homotopy.h₁
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro z
    exact False.elim z.1.property

/-- 全境界ホモトピーの各側面も、元の同じ全辺円柱そのもの。 -/
lemma triangleBoundaryHomotopy_face (i : Fin 3) :
    (SSet.boundary.ι i ▷ (Δ[1] : SSet.{u})) ≫ (triangleBoundaryHomotopy Hf Hg Hh).h =
      triangleBoundaryCylinderRawFaces Hf Hg Hh i :=
  triangleBoundaryCylinderMap_face Hf Hg Hh i

/-- 元の全三角形の三辺を貼った写像は、同じ全三角形の境界制限そのもの。 -/
lemma triangleBoundaryMap_of_compStruct (T : SSet.Edge.CompStruct f₁ g₁ h₁) :
    triangleBoundaryMap f₁ g₁ h₁ = (SSet.boundary 2).ι ≫ SSet.yonedaEquiv.symm T.simplex := by
  apply SSet.boundary.hom_ext
  intro i
  rw [triangleBoundaryMap_face, ← Category.assoc, SSet.boundary.ι_ι]
  fin_cases i
  · exact (SSet.Edge.CompStruct.δ_zero_yonedaEquiv_symm T).symm
  · exact (SSet.Edge.CompStruct.δ_one_yonedaEquiv_symm T).symm
  · exact (SSet.Edge.CompStruct.δ_two_yonedaEquiv_symm T).symm

end SerrePositivity.KST.SConstruction
