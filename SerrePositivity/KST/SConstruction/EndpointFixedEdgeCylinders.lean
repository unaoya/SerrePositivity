module
public import SerrePositivity.KST.SConstruction.EndpointFixedTriangleHomotopy
public import SerrePositivity.KST.SConstruction.RelativeTriangleTransport

/-! # 元の辺を結ぶ全端点固定円柱と共有頂点
概要：元の二辺を結ぶ円柱を全境界固定式と保存し、共有頂点での厳密な一致を回収する。
方針：区間境界の二面で固定式を評価し、元の始終頂点の等号を使う。
規約：端点だけの点ごとの 条件でなく、全頂点区間の実写像を保持する。
使われ方：三つの元の辺円柱を全三角形境界の円柱へ貼り合わせる。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 元の二辺全体を結び、元の区間境界を全時刻固定する円柱。 -/
structure EndpointFixedEdgeCylinder {E : SSet.{u}} {x y : E _⦋0⦌}
    (a b : E.Edge x y) where
  /-- 元の二辺の全区間を両端に持つ同じ実円柱。 -/
  homotopy : SSet.Homotopy (SSet.yonedaEquiv.symm a.edge) (SSet.yonedaEquiv.symm b.edge)
  /-- 全区間境界を全比較時刻で厳密に固定する。 -/
  relative : ((SSet.boundary 1).ι ▷ (Δ[1] : SSet.{u})) ≫ homotopy.h =
    fst (SSet.boundary 1).toSSet Δ[1] ≫ (SSet.boundary 1).ι ≫ SSet.yonedaEquiv.symm a.edge

/-- 同じ元の辺を全時刻固定する円柱。 -/
def endpointFixedEdgeCylinderRefl {E : SSet.{u}} {x y : E _⦋0⦌} (a : E.Edge x y) :
    EndpointFixedEdgeCylinder a a :=
  ⟨_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl (SSet.yonedaEquiv.symm a.edge), by
    change _ ≫ fst Δ[1] Δ[1] ≫ SSet.yonedaEquiv.symm a.edge = _
    rw [whiskerRight_fst_assoc]⟩

/-- 全境界固定円柱の各頂点区間を、その元の頂点の定数区間として回収する。 -/
lemma EndpointFixedEdgeCylinder.vertex {E : SSet.{u}} {x y : E _⦋0⦌}
    {a b : E.Edge x y} (H : EndpointFixedEdgeCylinder a b) (i : Fin 2) :
    (stdSimplex.δ i ▷ (Δ[1] : SSet.{u})) ≫ H.homotopy.h =
      fst (Δ[0] : SSet.{u}) Δ[1] ≫ stdSimplex.δ i ≫ SSet.yonedaEquiv.symm a.edge := by
  rw [← SSet.boundary.ι_ι i, comp_whiskerRight, Category.assoc, H.relative,
    whiskerRight_fst_assoc, Category.assoc, SSet.boundary.ι_ι_assoc]

/-- 元の辺円柱を、時刻の関数空間を値とする元の辺パラメータの全族へ移す。 -/
def EndpointFixedEdgeCylinder.curry {E : SSet.{u}} {x y : E _⦋0⦌}
    {a b : E.Edge x y} (H : EndpointFixedEdgeCylinder a b) :
    (Δ[1] : SSet.{u}) ⟶ (ihom (Δ[1] : SSet.{u})).obj E :=
  MonoidalClosed.curry ((β_ (Δ[1] : SSet.{u}) Δ[1]).hom ≫ H.homotopy.h)

/-- 頂点区間が同じ円柱の全 curry も、その同じ頂点で厳密に一致する。 -/
lemma endpointFixedEdgeCylinder_curry_vertex_eq {E : SSet.{u}}
    {x y z w : E _⦋0⦌} {a b : E.Edge x y} {c d : E.Edge z w}
    (H : EndpointFixedEdgeCylinder a b) (K : EndpointFixedEdgeCylinder c d) (i j : Fin 2)
    (h : (stdSimplex.δ i ▷ (Δ[1] : SSet.{u})) ≫ H.homotopy.h =
      (stdSimplex.δ j ▷ (Δ[1] : SSet.{u})) ≫ K.homotopy.h) :
    stdSimplex.δ i ≫ H.curry = stdSimplex.δ j ≫ K.curry := by
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_natural_left]
  change _ ◁ stdSimplex.δ i ≫ uncurry (MonoidalClosed.curry _) =
    _ ◁ stdSimplex.δ j ≫ uncurry (MonoidalClosed.curry _)
  rw [uncurry_curry, uncurry_curry, BraidedCategory.braiding_naturality_right_assoc,
    BraidedCategory.braiding_naturality_right_assoc, h]

end SerrePositivity.KST.SConstruction
