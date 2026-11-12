module
public import SerrePositivity.KST.SConstruction.EndpointFixedEdgeCylinders
public import SerrePositivity.KST.SConstruction.FixedBoundaryPostcomposition

/-! # 全端点固定辺円柱の同じ全射影
概要：元の辺円柱と全境界固定式を、同じ写像で後合成して保存する。
方針：辺の写像と Yoneda 表示の自然性で、円柱の両端を厳密に合わせる。
規約：元の全円柱の像を保持し、新しい比較辺を選ばない。
使われ方：生成第四辺と指定 BF 比較辺の問題を、元の raw 射影へ移す。
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

/-- 始点の表示だけを移し、元の全一単体の等号を同じデータに保持する。 -/
def edgeSourceTransportData {E : SSet.{u}} {x x' y : E _⦋0⦌}
    (a : E.Edge x y) (h : x = x') : {b : E.Edge x' y // b.edge = a.edge} :=
  ⟨a.ofEq h rfl, rfl⟩

/-- 元の両端固定円柱の同じ全後合成像。 -/
def EndpointFixedEdgeCylinder.postcomp {E B : SSet.{u}} {x y : E _⦋0⦌}
    {a b : E.Edge x y} (H : EndpointFixedEdgeCylinder a b) (p : E ⟶ B) :
    EndpointFixedEdgeCylinder (a.map p) (b.map p) where
  homotopy := familyHomotopyEndpointTransport (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp H.homotopy p)
    (SSet.yonedaEquiv_symm_comp a.edge p).symm (SSet.yonedaEquiv_symm_comp b.edge p)
  relative := by
    rw [familyHomotopyEndpointTransport_h]
    change _ ≫ H.homotopy.h ≫ p = _
    rw [← Category.assoc, H.relative, Category.assoc, Category.assoc,
      SSet.yonedaEquiv_symm_comp]
    rfl

/-- 射影した全円柱は、元の同じ全円柱の後合成そのもの。 -/
lemma EndpointFixedEdgeCylinder.postcomp_h {E B : SSet.{u}} {x y : E _⦋0⦌}
    {a b : E.Edge x y} (H : EndpointFixedEdgeCylinder a b) (p : E ⟶ B) :
    (H.postcomp p).homotopy.h = H.homotopy.h ≫ p :=
  familyHomotopyEndpointTransport_h _ _ _

/-- 同じ実写像の表示等号に沿い、元の全辺円柱を写像像の型だけ移す。 -/
def endpointFixedCylinderMapTransport {E B : SSet.{u}} {x y : E _⦋0⦌}
    (a b : E.Edge x y) {p q : E ⟶ B} (h : p = q)
    (H : EndpointFixedEdgeCylinder (a.map q) (b.map q)) :
    EndpointFixedEdgeCylinder (a.map p) (b.map p) := by
  cases h
  exact H

/-- 写像の表示移送でも、元の全実円柱をそのまま保持する。 -/
lemma endpointFixedCylinderMapTransport_h {E B : SSet.{u}} {x y : E _⦋0⦌}
    (a b : E.Edge x y) {p q : E ⟶ B} (h : p = q)
    (H : EndpointFixedEdgeCylinder (a.map q) (b.map q)) :
    (endpointFixedCylinderMapTransport a b h H).homotopy.h = H.homotopy.h := by
  cases h
  rfl

end SerrePositivity.KST.SConstruction
