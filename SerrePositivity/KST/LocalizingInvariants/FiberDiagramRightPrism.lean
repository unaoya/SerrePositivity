module
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.HomotopyEdgeTriangleUpperFaces

public import SerrePositivity.KST.LocalizingInvariants.FiberDiagramPrism
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.HomotopyEdgeTriangleLowerFaces

/-!
概要：任意の fiber 図式比較の右辺の正方形を、元の二三角形と対角辺として保持する。
方針：比較ホモトピーの右辺上の上下三角形と、同じ区間に沿う対角辺を取る。
規約：三角形と頂点比較を選び直さない。使われ方：全 BF 写像空間での指定区間の抽出。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.FiberDiagram

def domainRight := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareRightArrow (𝟙 ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1]))

variable {D E : FiberDiagram.{u}} (f : D ⟶ E)

def rightDiagonal : Sp.Edge (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex D.triangle.square 1 0)
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex E.triangle.square 1 1) := by
  let e := domainRight.{u}.tensor _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge
  let e' := e.map ((truncation 2).map (comparisonHomotopy f).h)
  refine SSet.Edge.mk e'.edge ?_ ?_
  · exact e'.src_eq.trans (ConcreteCategory.congr_hom
      (NatTrans.congr_app (comparisonHomotopy f).h₀ (Opposite.op ⦋0⦌)) _)
  · exact e'.tgt_eq.trans (ConcreteCategory.congr_hom
      (NatTrans.congr_app (comparisonHomotopy f).h₁ (Opposite.op ⦋0⦌)) _)

def rightUpper : Sp.{u} _⦋2⦌ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.homotopyEdgeTriangleUpper (comparisonHomotopy f).h domainRight.edge

def rightLower : Sp.{u} _⦋2⦌ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.homotopyEdgeTriangleLower (comparisonHomotopy f).h domainRight.edge

lemma rightUpper_two : Sp.δ 2 (rightUpper f) = (comparisonEdge f 1 0).edge := by
  rw [rightUpper, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.homotopyEdgeTriangleUpper_two]
  rw [show ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1]).δ 1 domainRight.edge =
    (stdSimplex.obj₀Equiv.symm 1, stdSimplex.obj₀Equiv.symm 0) from domainRight.src_eq]
  rfl

lemma rightUpper_zero : Sp.δ 0 (rightUpper f) = (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareRightArrow E.triangle.square).edge := by
  rw [rightUpper, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.homotopyEdgeTriangleUpper_zero]
  rfl

lemma rightLower_two : Sp.δ 2 (rightLower f) = (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareRightArrow D.triangle.square).edge := by
  rw [rightLower, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.homotopyEdgeTriangleLower_two]
  rfl

lemma rightLower_zero : Sp.δ 0 (rightLower f) = (comparisonEdge f 1 1).edge := by
  rw [rightLower, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.homotopyEdgeTriangleLower_zero]
  rw [show ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1]).δ 0 domainRight.edge =
    (stdSimplex.obj₀Equiv.symm 1, stdSimplex.obj₀Equiv.symm 1) from domainRight.tgt_eq]
  rfl

lemma rightUpper_one : Sp.δ 1 (rightUpper f) = (rightDiagonal f).edge := by
  rw [rightUpper, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.homotopyEdgeTriangleUpper_one]
  change (comparisonHomotopy f).h.app _ (domainRight.edge, _) =
    (comparisonHomotopy f).h.app _ (domainRight.edge, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.homotopyIntervalEdge_simplex]

lemma rightLower_one : Sp.δ 1 (rightLower f) = (rightDiagonal f).edge := by
  rw [rightLower, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.homotopyEdgeTriangleLower_one,
    ← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.homotopyEdgeTriangleUpper_one (comparisonHomotopy f).h domainRight.edge]
  exact rightUpper_one f

end SerrePositivity.KST.LocalizingInvariants.FiberDiagram
