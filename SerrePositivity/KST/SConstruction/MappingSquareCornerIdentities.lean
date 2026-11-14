module
public import SerrePositivity.KST.SConstruction.MappingCellEdges

/-! # 元の共有辺と定数辺からの角の厳密な照合
概要：元の辺の等号を端点で評価し、貼り合わせの六頂点を照合する。
方針：同じ零単体で境界射を評価する。
規約：頂点の同型でなく等号を使い、全区間の保持とは区別する。
使われ方：端点の表示を合わせた三正方形データの実構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 共有する垂直区間の、各指定端点の等号。 -/
lemma mappingSquareVertical_shared_corner {E : SSet.{u}}
    {Q R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ E} (a b : Fin 2)
    (h : pastingSquareVertical a ≫ Q = pastingSquareVertical a ≫ R) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex Q a b = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex R a b := by
  exact congrArg (fun f => f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm b)) h

/-- 共有する水平区間の、各指定端点の等号。 -/
lemma mappingSquareHorizontal_shared_corner {E : SSet.{u}}
    {Q R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ E} (a b : Fin 2)
    (h : pastingSquareHorizontal b ≫ Q = pastingSquareHorizontal b ≫ R) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex Q a b = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex R a b := by
  exact congrArg (fun f => f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm a)) h

/-- 元の定数垂直辺の、各指定端点の回収。 -/
lemma mappingSquareVertical_constant_corner {E : SSet.{u}}
    {Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ E} (a b : Fin 2) (v : E _⦋0⦌)
    (h : pastingSquareVertical a ≫ Q = SSet.const v) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex Q a b = v := by
  have hh := congrArg (fun f => f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm b)) h
  have hc : (SSet.const v : (Δ[1] : SSet.{u}) ⟶ E).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm b) = v := by
    simp only [SSet.const_app, SimplexCategory.const_eq_id, op_id,
      CategoryTheory.Functor.map_id_apply]
    rfl
  exact hh.trans hc

/-- 元の定数水平辺の、各指定端点の回収。 -/
lemma mappingSquareHorizontal_constant_corner {E : SSet.{u}}
    {Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ E} (a b : Fin 2) (v : E _⦋0⦌)
    (h : pastingSquareHorizontal b ≫ Q = SSet.const v) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex Q a b = v := by
  have hh := congrArg (fun f => f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm a)) h
  have hc : (SSet.const v : (Δ[1] : SSet.{u}) ⟶ E).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm a) = v := by
    simp only [SSet.const_app, SimplexCategory.const_eq_id, op_id,
      CategoryTheory.Functor.map_id_apply]
    rfl
  exact hh.trans hc

/-- 指定された恒等辺の全区間は、その頂点の定数族。 -/
lemma mappingIdentityEdge_map {E : SSet.{u}} (v : E _⦋0⦌) :
    SSet.yonedaEquiv.symm (SSet.Edge.id v).edge = SSet.const v := by
  change SSet.yonedaEquiv.symm (E.σ 0 v) = SSet.const v
  rw [← stdSimplex.σ_comp_yonedaEquiv_symm, SSet.yonedaEquiv_symm_zero]
  simp only [SSet.comp_const]

/-- 三角形の指定面の射の等号を、同じ raw な一単体の等号に戻す。 -/
lemma mappingTriangleFaceEdge {E : SSet.{u}} {a b : E _⦋0⦌} (t : (Δ[2] : SSet.{u}) ⟶ E)
    (i : Fin 3) (e : E.Edge a b) (h : stdSimplex.δ i ≫ t = SSet.yonedaEquiv.symm e.edge) :
    E.δ i (SSet.yonedaEquiv t) = e.edge := by
  rw [← stdSimplex.yonedaEquiv_δ_comp, h, Equiv.apply_symm_apply]

end SerrePositivity.KST.SConstruction
