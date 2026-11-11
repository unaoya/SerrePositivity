module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.RoofSliceTriangleInverse
public import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits

/-! # 実 over の三辺が指定する元の三次外ホーン

概要：指定実辺と二つの始錐の脚から、元の圏の最後の面が欠けた三次ホーンを作る。
方針：三つの実 over 辺の合成三角形を、共通の分母辺上で厳密に貼る。
規約：元の図式と二脚を全て保持。充填可能性は仮定しない。
使われ方：有限 ∞ 図式の始錐の一次整合性の具体的な境界。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet
open scoped _root_.Simplicial
variable {X : SSet.{u}} (a : Δ[0] ⟶ X) {s₀ s₁ s₂ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver a) _⦋0⦌}

/-- 実 over 辺の合成三角形の一面は、指定始端の分母辺。 -/
lemma roofPointSliceTriangle_edge_source
    (e : Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver a)) s₀ s₁) :
    SSet.stdSimplex.δ (1 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTriangle a e.edge =
      (SSet.yonedaEquiv (X := X)).symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceVertexEdge a s₀).edge := by
  apply (SSet.yonedaEquiv (X := X)).injective
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTriangle_leg a (e.edge : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver a) _⦋1⦌) 1).trans
    ((congrArg (fun s => (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceVertexEdge a s).edge) e.src_eq).trans
      ((SSet.yonedaEquiv (X := X)).apply_symm_apply _).symm)

/-- 実 over 辺の合成三角形の零面は、指定終端の分母辺。 -/
lemma roofPointSliceTriangle_edge_target
    (e : Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver a)) s₀ s₁) :
    SSet.stdSimplex.δ (0 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTriangle a e.edge =
      (SSet.yonedaEquiv (X := X)).symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceVertexEdge a s₁).edge := by
  apply (SSet.yonedaEquiv (X := X)).injective
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTriangle_leg a (e.edge : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver a) _⦋1⦌) 0).trans
    ((congrArg (fun s => (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceVertexEdge a s).edge) e.tgt_eq).trans
      ((SSet.yonedaEquiv (X := X)).apply_symm_apply _).symm)

variable (e₀₁ : Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver a)) s₀ s₁)
variable (e₁₂ : Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver a)) s₁ s₂)
variable (e₀₂ : Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver a)) s₀ s₂)

/-- 最後の面を除く三面は、指定図式辺と二脚の三角形。 -/
def roofPointSliceOuterHornFace (i : Fin 4) (_hi : i ≠ 3) : Δ[2] ⟶ X :=
  if i = 0 then _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTriangle a e₁₂.edge
  else if i = 1 then _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTriangle a e₀₂.edge
  else _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTriangle a e₀₁.edge

/-- 三つの指定合成三角形は、三つの共通分母辺上で厳密に一致する。 -/
lemma roofPointSliceOuterHorn_compatible :
    horn.IsCompatible (roofPointSliceOuterHornFace a e₀₁ e₁₂ e₀₂) := by
  rw [horn.isCompatible_iff]
  intro i j hi hj hij
  fin_cases i <;> fin_cases j
  all_goals try exact (hi (by decide)).elim
  all_goals try exact (hj (by decide)).elim
  all_goals try exact False.elim ((by decide : ¬ ((0 : Fin 4) < 0)) hij)
  all_goals try exact False.elim ((by decide : ¬ ((1 : Fin 4) < 0)) hij)
  all_goals try exact False.elim ((by decide : ¬ ((1 : Fin 4) < 1)) hij)
  all_goals try exact False.elim ((by decide : ¬ ((2 : Fin 4) < 0)) hij)
  all_goals try exact False.elim ((by decide : ¬ ((2 : Fin 4) < 1)) hij)
  all_goals try exact False.elim ((by decide : ¬ ((2 : Fin 4) < 2)) hij)
  · change SSet.stdSimplex.δ (0 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTriangle a e₁₂.edge =
      SSet.stdSimplex.δ (0 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTriangle a e₀₂.edge
    rw [roofPointSliceTriangle_edge_target, roofPointSliceTriangle_edge_target]
  · change SSet.stdSimplex.δ (1 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTriangle a e₁₂.edge =
      SSet.stdSimplex.δ (0 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTriangle a e₀₁.edge
    rw [roofPointSliceTriangle_edge_source, roofPointSliceTriangle_edge_target]
  · change SSet.stdSimplex.δ (1 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTriangle a e₀₂.edge =
      SSet.stdSimplex.δ (1 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTriangle a e₀₁.edge
    rw [roofPointSliceTriangle_edge_source, roofPointSliceTriangle_edge_source]

/-- 指定図式辺と二脚を保持する、元の圏の三次最後外ホーン。 -/
def roofPointSliceOuterHorn : (Λ[3, 3] : SSet.{u}) ⟶ X :=
  (roofPointSliceOuterHorn_compatible a e₀₁ e₁₂ e₀₂).desc

/-- 零面は元の指定図式辺の合成三角形。 -/
lemma roofPointSliceOuterHorn_face0 :
    horn.ι (3 : Fin 4) 0 (by decide) ≫ roofPointSliceOuterHorn a e₀₁ e₁₂ e₀₂ =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTriangle a e₁₂.edge := by
  exact (horn.IsCompatible.ι_desc (roofPointSliceOuterHorn_compatible a e₀₁ e₁₂ e₀₂)
    0 (by decide)).trans (ite_eq_left rfl)

/-- 一面は第二脚の合成三角形。 -/
lemma roofPointSliceOuterHorn_face1 :
    horn.ι (3 : Fin 4) 1 (by decide) ≫ roofPointSliceOuterHorn a e₀₁ e₁₂ e₀₂ =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTriangle a e₀₂.edge := by
  exact (horn.IsCompatible.ι_desc (roofPointSliceOuterHorn_compatible a e₀₁ e₁₂ e₀₂)
    1 (by decide)).trans ((ite_eq_right (by decide)).trans (ite_eq_left rfl))

/-- 二面は第一脚の合成三角形。 -/
lemma roofPointSliceOuterHorn_face2 :
    horn.ι (3 : Fin 4) 2 (by decide) ≫ roofPointSliceOuterHorn a e₀₁ e₁₂ e₀₂ =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTriangle a e₀₁.edge := by
  exact (horn.IsCompatible.ι_desc (roofPointSliceOuterHorn_compatible a e₀₁ e₁₂ e₀₂)
    2 (by decide)).trans ((ite_eq_right (by decide)).trans (ite_eq_right (by decide)))

end SerrePositivity.InfinityCategories.Project.DerivedCategories
