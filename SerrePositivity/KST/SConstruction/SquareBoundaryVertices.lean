module
public import SerrePositivity.KST.SConstruction.ClosedSubcategoryPullbacks

/-! # 指定された辺の四角形の端点
概要：fiber/cofiber 四角形の指定辺から周囲の二つの端点を厳密に回収する。
方針：Yoneda 射を二つの標準頂点で評価する。
規約：端点の同型でなく等号。使われ方：全部分圏への普遍四角形の持ち上げ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 辺の Yoneda 射の始点は指定された始域。 -/
lemma yonedaEdge_source {X : SSet.{u}} {x y : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x y) :
    (SSet.yonedaEquiv.symm f.edge).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) = x := by
  have h := congrArg SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSimplex_source f)
  rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] at h
  have hδ : SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 2) :
      (Δ[0] : SSet.{u}) ⟶ Δ[1]) = stdSimplex.obj₀Equiv.symm (0 : Fin 2) := by decide
  rw [hδ] at h
  exact h

/-- 辺の Yoneda 射の終点は指定された終域。 -/
lemma yonedaEdge_target {X : SSet.{u}} {x y : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x y) :
    (SSet.yonedaEquiv.symm f.edge).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = y := by
  have h := congrArg SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSimplex_target f)
  rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] at h
  have hδ : SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2) :
      (Δ[0] : SSet.{u}) ⟶ Δ[1]) = stdSimplex.obj₀Equiv.symm (1 : Fin 2) := by decide
  rw [hδ] at h
  exact h

/-- 下辺を指定した四角形の二つの下角は辺の端点。 -/
lemma square_bottom_vertices {X : SSet.{u}} {x y : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x y)
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X)
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ F = SSet.yonedaEquiv.symm f.edge) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex F 0 0 = x ∧ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex F 1 0 = y := by
  exact ⟨(ConcreteCategory.congr_hom (NatTrans.congr_app h (Opposite.op ⦋0⦌))
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2))).trans (yonedaEdge_source f),
    (ConcreteCategory.congr_hom (NatTrans.congr_app h (Opposite.op ⦋0⦌))
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2))).trans (yonedaEdge_target f)⟩

/-- 右辺を指定した四角形の二つの右角は辺の端点。 -/
lemma square_right_vertices {X : SSet.{u}} {x y : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x y)
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X)
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ F = SSet.yonedaEquiv.symm f.edge) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex F 1 0 = x ∧ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex F 1 1 = y := by
  exact ⟨(ConcreteCategory.congr_hom (NatTrans.congr_app h (Opposite.op ⦋0⦌))
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2))).trans (yonedaEdge_source f),
    (ConcreteCategory.congr_hom (NatTrans.congr_app h (Opposite.op ⦋0⦌))
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2))).trans (yonedaEdge_target f)⟩

end SerrePositivity.KST.SConstruction
