module
public import SerrePositivity.KST.SConstruction.TriangleBoundaryHomotopy
public import SerrePositivity.KST.SConstruction.RelativeTriangleTransportFromZero

/-! # 指定した三辺円柱に沿う全三角形の相対移送
概要：三辺円柱の始端にある元の全三角形を保持し、終端三辺を持つ実三角形を作る。
方針：元の全境界ホモトピーと時刻零の全三角形に相対延長を適用する。
規約：任意の全境界充填を仮定せず、元の全三角形を比較円柱の始端に保持する。
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
  (Hh : EndpointFixedEdgeCylinder h₀ h₁) (T : SSet.Edge.CompStruct f₀ g₀ h₀)

/-- 元の全三角形境界を始端に持つ、入力三辺円柱の同じ全境界ホモトピー。 -/
def triangleEdgeTransportFromZeroBoundary :
    Homotopy ((SSet.boundary 2).ι ≫ SSet.yonedaEquiv.symm T.simplex)
      (triangleBoundaryMap f₁ g₁ h₁) :=
  familyHomotopyEndpointTransport (triangleBoundaryHomotopy Hf Hg Hh)
    (triangleBoundaryMap_of_compStruct T).symm rfl

/-- 指定した終端三辺を持ち、元の全三角形から相対移送された実合成三角形。 -/
def triangleEdgeTransportFromZero : SSet.Edge.CompStruct f₁ g₁ h₁ :=
  SSet.Edge.CompStruct.mk
    (triangleTransportFromZero T.simplex _ (triangleEdgeTransportFromZeroBoundary Hf Hg Hh T))
    (by rw [triangleTransportFromZero_face, triangleBoundaryMap_face];
        exact SSet.yonedaEquiv.apply_symm_apply f₁.edge)
    (by rw [triangleTransportFromZero_face, triangleBoundaryMap_face];
        exact SSet.yonedaEquiv.apply_symm_apply g₁.edge)
    (by rw [triangleTransportFromZero_face, triangleBoundaryMap_face];
        exact SSet.yonedaEquiv.apply_symm_apply h₁.edge)

/-- 元の同じ全三角形から移送した全三角形への実比較円柱。 -/
def triangleEdgeTransportFromZeroComparison : Homotopy
    (SSet.yonedaEquiv.symm T.simplex)
    (SSet.yonedaEquiv.symm (triangleEdgeTransportFromZero Hf Hg Hh T).simplex) :=
  triangleTransportFromZeroComparison T.simplex _ (triangleEdgeTransportFromZeroBoundary Hf Hg Hh T)

/-- 元の三辺円柱を、全三角形比較の全境界として厳密に回収する。 -/
lemma triangleEdgeTransportFromZeroComparison_boundary :
    ((SSet.boundary 2).ι ▷ (Δ[1] : SSet.{u})) ≫
        (triangleEdgeTransportFromZeroComparison Hf Hg Hh T).h =
      (triangleBoundaryHomotopy Hf Hg Hh).h := by
  rw [triangleEdgeTransportFromZeroComparison, triangleTransportFromZeroComparison_boundary]
  exact familyHomotopyEndpointTransport_h _ _ _

/-- 全三角形比較の各側面は、入力した元の同じ全辺円柱そのもの。 -/
lemma triangleEdgeTransportFromZeroComparison_face (i : Fin 3) :
    (stdSimplex.δ i ▷ (Δ[1] : SSet.{u})) ≫
        (triangleEdgeTransportFromZeroComparison Hf Hg Hh T).h =
      triangleBoundaryCylinderRawFaces Hf Hg Hh i := by
  rw [← SSet.boundary.ι_ι i, comp_whiskerRight, Category.assoc,
    triangleEdgeTransportFromZeroComparison_boundary, triangleBoundaryHomotopy_face]

/-- 対角辺の入力円柱が定数なら、全三角形比較でも対角辺全体を厳密に固定する。 -/
lemma triangleEdgeTransportFromZeroComparison_fixed_diagonal
    (h : Hh.homotopy.h = fst (Δ[1] : SSet.{u}) Δ[1] ≫ SSet.yonedaEquiv.symm h₀.edge) :
    (stdSimplex.δ 1 ▷ (Δ[1] : SSet.{u})) ≫
        (triangleEdgeTransportFromZeroComparison Hf Hg Hh T).h =
      fst (Δ[1] : SSet.{u}) Δ[1] ≫ SSet.yonedaEquiv.symm h₀.edge := by
  rw [triangleEdgeTransportFromZeroComparison_face]
  exact h

end SerrePositivity.KST.SConstruction
