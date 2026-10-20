module
public import SerrePositivity.KST.SConstruction.TriangleBoundaryHomotopy

/-! # 指定した三辺円柱に沿う全三角形の相対移送
概要：三辺円柱の終端にある元の全三角形を保持し、始端三辺を持つ実三角形を作る。
方針：元の全境界ホモトピーと時刻一の全三角形に相対延長を適用する。
規約：任意の全境界充填を仮定せず、元の全三角形を比較円柱の終端に保持する。
使われ方：三入力の二三角形の三辺を元の BF 比較へ移し、共有対角辺を固定する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
variable {E : SSet.{u}} [KanComplex E] {x y z : E _⦋0⦌}
  {f₀ f₁ : E.Edge x y} {g₀ g₁ : E.Edge y z} {h₀ h₁ : E.Edge x z}
  (Hf : EndpointFixedEdgeCylinder f₀ f₁) (Hg : EndpointFixedEdgeCylinder g₀ g₁)
  (Hh : EndpointFixedEdgeCylinder h₀ h₁) (T : SSet.Edge.CompStruct f₁ g₁ h₁)

/-- 元の全三角形境界を終端に持つ、入力三辺円柱の同じ全境界ホモトピー。 -/
def triangleEdgeTransportBoundary :
    Homotopy (triangleBoundaryMap f₀ g₀ h₀)
      ((SSet.boundary 2).ι ≫ SSet.yonedaEquiv.symm T.simplex) :=
  familyHomotopyEndpointTransport (triangleBoundaryHomotopy Hf Hg Hh) rfl
    (triangleBoundaryMap_of_compStruct T)

/-- 指定した始端三辺を持ち、元の全三角形から相対移送された実合成三角形。 -/
def triangleEdgeTransport : SSet.Edge.CompStruct f₀ g₀ h₀ :=
  SSet.Edge.CompStruct.mk
    (triangleTransportFromOne T.simplex _ (triangleEdgeTransportBoundary Hf Hg Hh T))
    (by rw [triangleTransportFromOne_face, triangleBoundaryMap_face];
        exact SSet.yonedaEquiv.apply_symm_apply f₀.edge)
    (by rw [triangleTransportFromOne_face, triangleBoundaryMap_face];
        exact SSet.yonedaEquiv.apply_symm_apply g₀.edge)
    (by rw [triangleTransportFromOne_face, triangleBoundaryMap_face];
        exact SSet.yonedaEquiv.apply_symm_apply h₀.edge)

/-- 移送した全三角形から元の同じ全三角形へ戻る実比較円柱。 -/
def triangleEdgeTransportComparison : Homotopy
    (SSet.yonedaEquiv.symm (triangleEdgeTransport Hf Hg Hh T).simplex)
    (SSet.yonedaEquiv.symm T.simplex) :=
  triangleTransportFromOneComparison T.simplex _ (triangleEdgeTransportBoundary Hf Hg Hh T)

/-- 元の三辺円柱を、全三角形比較の全境界として厳密に回収する。 -/
lemma triangleEdgeTransportComparison_boundary :
    ((SSet.boundary 2).ι ▷ (Δ[1] : SSet.{u})) ≫
        (triangleEdgeTransportComparison Hf Hg Hh T).h =
      (triangleBoundaryHomotopy Hf Hg Hh).h := by
  rw [triangleEdgeTransportComparison, triangleTransportFromOneComparison_boundary]
  exact familyHomotopyEndpointTransport_h _ _ _

/-- 全三角形比較の各側面は、入力した元の同じ全辺円柱そのもの。 -/
lemma triangleEdgeTransportComparison_face (i : Fin 3) :
    (stdSimplex.δ i ▷ (Δ[1] : SSet.{u})) ≫
        (triangleEdgeTransportComparison Hf Hg Hh T).h =
      triangleBoundaryCylinderRawFaces Hf Hg Hh i := by
  rw [← SSet.boundary.ι_ι i, comp_whiskerRight, Category.assoc,
    triangleEdgeTransportComparison_boundary, triangleBoundaryHomotopy_face]

/-- 対角辺の入力円柱が定数なら、全三角形比較でも対角辺全体を厳密に固定する。 -/
lemma triangleEdgeTransportComparison_fixed_diagonal
    (h : Hh.homotopy.h = fst (Δ[1] : SSet.{u}) Δ[1] ≫ SSet.yonedaEquiv.symm h₀.edge) :
    (stdSimplex.δ 1 ▷ (Δ[1] : SSet.{u})) ≫
        (triangleEdgeTransportComparison Hf Hg Hh T).h =
      fst (Δ[1] : SSet.{u}) Δ[1] ≫ SSet.yonedaEquiv.symm h₀.edge := by
  rw [triangleEdgeTransportComparison_face]
  exact h

end SerrePositivity.KST.SConstruction
