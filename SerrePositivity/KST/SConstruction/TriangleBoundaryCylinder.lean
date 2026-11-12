module
public import SerrePositivity.KST.SConstruction.EndpointFixedEdgeCylinders
public import SerrePositivity.KST.SConstruction.TriangleBoundaryMaps

/-! # 三つの全端点固定円柱を元の全三角形境界へ貼る
概要：元の三つの辺円柱を、共有頂点を厳密に保つ一つの全三角形境界円柱へ貼る。
方針：時刻 Hom を値とする curry の三面を、三角形境界の余極限で貼り合わせる。
規約：元の全円柱を各側面でそのまま回収する。Kan 性や充填はここでは使わない。
使われ方：三入力の元の BF 比較辺へ移すための具体的な相対三角形移送の境界。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet Spectra
open scoped Simplicial
variable {E : SSet.{u}} {x y z : E _⦋0⦌}
  {f₀ f₁ : E.Edge x y} {g₀ g₁ : E.Edge y z} {h₀ h₁ : E.Edge x z}
  (Hf : EndpointFixedEdgeCylinder f₀ f₁) (Hg : EndpointFixedEdgeCylinder g₀ g₁)
  (Hh : EndpointFixedEdgeCylinder h₀ h₁)

/-- 元の三円柱を時刻 Hom の族として面番号順に並べる。 -/
def triangleBoundaryCylinderFaces : Fin 3 →
    ((Δ[1] : SSet.{u}) ⟶ (ihom (Δ[1] : SSet.{u})).obj E) :=
  ![Hg.curry, Hh.curry, Hf.curry]

/-- 全端点固定の式から、元の三円柱は共有頂点区間上で厳密に一致する。 -/
lemma triangleBoundaryCylinderFaces_compatible :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.IsCompatible (triangleBoundaryCylinderFaces Hf Hg Hh) := by
  intro j k hjk
  fin_cases j
  · fin_cases k
    · exact False.elim ((by decide : ¬ ((0 : Fin 3) < 0)) hjk)
    · change stdSimplex.δ 0 ≫ Hg.curry = stdSimplex.δ 0 ≫ Hh.curry
      apply endpointFixedEdgeCylinder_curry_vertex_eq
      rw [Hg.vertex, Hh.vertex, SSet.Edge.δ_zero_yonedaEquiv_symm,
        SSet.Edge.δ_zero_yonedaEquiv_symm]
    · change stdSimplex.δ 1 ≫ Hg.curry = stdSimplex.δ 0 ≫ Hf.curry
      apply endpointFixedEdgeCylinder_curry_vertex_eq
      rw [Hg.vertex, Hf.vertex, SSet.Edge.δ_one_yonedaEquiv_symm,
        SSet.Edge.δ_zero_yonedaEquiv_symm]
  · fin_cases k
    · exact False.elim ((by decide : ¬ ((1 : Fin 3) < 0)) hjk)
    · exact False.elim ((by decide : ¬ ((1 : Fin 3) < 1)) hjk)
    · change stdSimplex.δ 1 ≫ Hh.curry = stdSimplex.δ 1 ≫ Hf.curry
      apply endpointFixedEdgeCylinder_curry_vertex_eq
      rw [Hh.vertex, Hf.vertex, SSet.Edge.δ_one_yonedaEquiv_symm,
        SSet.Edge.δ_one_yonedaEquiv_symm]
  · fin_cases k
    · exact False.elim ((by decide : ¬ ((2 : Fin 3) < 0)) hjk)
    · exact False.elim ((by decide : ¬ ((2 : Fin 3) < 1)) hjk)
    · exact False.elim ((by decide : ¬ ((2 : Fin 3) < 2)) hjk)

/-- 元の三円柱を一つに貼った、同じ全三角形境界円柱の実写像。 -/
def triangleBoundaryCylinderMap : (∂Δ[2] : SSet.{u}) ⊗ Δ[1] ⟶ E :=
  (β_ (Δ[1] : SSet.{u}) (∂Δ[2] : SSet.{u})).inv ≫
    uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.desc (triangleBoundaryCylinderFaces_compatible Hf Hg Hh))

/-- 元の三つの全円柱の実写像を、面番号順に保存する。 -/
def triangleBoundaryCylinderRawFaces : Fin 3 → ((Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ E) :=
  ![Hg.homotopy.h, Hh.homotopy.h, Hf.homotopy.h]

/-- 貼った全境界円柱の各側面は、元の同じ全円柱そのもの。 -/
lemma triangleBoundaryCylinderMap_face (i : Fin 3) :
    (SSet.boundary.ι i ▷ (Δ[1] : SSet.{u})) ≫ triangleBoundaryCylinderMap Hf Hg Hh =
      triangleBoundaryCylinderRawFaces Hf Hg Hh i := by
  rw [triangleBoundaryCylinderMap, ← Category.assoc,
    BraidedCategory.braiding_inv_naturality_left, Category.assoc,
    ← uncurry_natural_left, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.ι_desc]
  fin_cases i <;> simp [triangleBoundaryCylinderFaces, triangleBoundaryCylinderRawFaces,
    EndpointFixedEdgeCylinder.curry]

end SerrePositivity.KST.SConstruction
