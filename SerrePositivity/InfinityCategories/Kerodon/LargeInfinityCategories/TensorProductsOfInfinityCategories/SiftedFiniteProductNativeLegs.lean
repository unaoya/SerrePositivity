module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SiftedFiniteProductNativeCone
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanConeHomotopyTriangles
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.HomotopyVerticalRestriction
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.F1BKanComplexHomotopyClasses

/-!
概要：元の有限 fiber 積の全空間 Kan 模型の native 積錐の全脚。
方針：同じ全錐円柱の両三角形から、全 native 脚を元の射影の Kan 像と照合する。
規約：全因子について元の一単体とホモトピーを保持する。
使われ方：P_Σ の sifted 余極限閉性の全有限積比較。

対応節は Kerodon 9.7（Tag 06ZD）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories
variable (n : ℕ) {B : SSet.{u}} [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.IsSiftedInfinity B] {E : Fin (n + 1) → SSet.{u}}
  (p : (i : Fin (n + 1)) → E i ⟶ B) (hp : ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (p i))

/-- 元の全錐円柱の頂点辺は、元の全有限積比較と同じ全一単体。 -/
lemma finiteSiftedProductNativeConeHomotopy_apexEdge :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneHomotopyApexEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.finiteSiftedProductNativeConeHomotopy n p hp)).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.finiteTotalComparisonKanMap n p)).edge := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.homotopyVertexEdge_prism (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.finiteSiftedProductNativeConeHomotopy n p hp)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl _ _) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.finiteTotalComparisonApexPrism n p)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.finiteSiftedProductNativeConeHomotopy_apex n p hp) (SSet.yonedaEquiv (𝟙 _))
  exact h.trans (SSet.yonedaEquiv_symm_app_id
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.finiteTotalComparisonKanMap n p)).edge)

/-- 全錐円柱の各底辺は、元の全空間 Kan 模型の恒等辺そのもの。 -/
lemma finiteSiftedProductNativeConeHomotopy_diagramEdge
    (i : Discrete (ULift.{u} (Fin (n + 1)))) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneHomotopyDiagramEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.finiteSiftedProductNativeConeHomotopy n p hp)
      (ULift.up (ComposableArrows.mk₀ i))).edge =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge
          (𝟙 ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteKanProductDiagram n (fun i ↦ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.continuousKanObject (E i))).obj i))).edge := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.homotopyVertexEdge_constant (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.finiteSiftedProductNativeConeHomotopy n p hp)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr _ _) _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.finiteSiftedProductNativeConeHomotopy_diagram n p hp)
    (ULift.up (ComposableArrows.mk₀ i))
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneHomotopyDiagramEdge _ _).edge = _ at h
  have hv := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve_vertex
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteKanProductDiagram n (fun i ↦ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.continuousKanObject (E i))) i).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityVertex_eq_coherent _)
  exact h.trans ((congrArg (fun v ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant v 1) hv).trans
    (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge_id, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one]; rfl))

/-- 元の native 積錐の各脚を、元の全空間 Kan 対象からの射として読み戻す。 -/
def finiteSiftedProductNativeKanLeg (i : Discrete (ULift.{u} (Fin (n + 1)))) :
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.continuousKanObject (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.finiteCommonFiberProduct n p) ⟶
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteKanProductDiagram n (fun i ↦ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.continuousKanObject (E i))).obj i :=
  _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.kanNativeConeLeg (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.finiteSiftedProductNativeCone n p hp) _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.finiteSiftedProductNativeCone_vertex n p hp) i

/-- 元の全 native 脚は、それぞれ元の共通 fiber 積射影の Kan 像にホモトピック。 -/
lemma finiteSiftedProductNativeKanLeg_projection
    (i : Discrete (ULift.{u} (Fin (n + 1)))) :
    Nonempty (SSet.Homotopy (finiteSiftedProductNativeKanLeg n p hp i)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.finiteCommonFiberProductProjection n p i.as.down))) := by
  let K := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.continuousKanObject (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.finiteCommonFiberProduct n p)
  let L := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteKanProductObject n (fun i ↦ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.continuousKanObject (E i))
  let hc := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.finiteSiftedProductNativeCone_vertex n p hp
  let hd := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteKanProductNativeCone_vertex n (fun i ↦ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.continuousKanObject (E i))
  let a := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.finiteTotalComparisonKanMap n p
  let H := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.finiteSiftedProductNativeConeHomotopy n p hp
  let low := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.kanConeHomotopyLower H K hc i (𝟙 _)
    (finiteSiftedProductNativeConeHomotopy_diagramEdge n p hp i)
  let up := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.kanConeHomotopyUpper H K L hc hd i a
    (finiteSiftedProductNativeConeHomotopy_apexEdge n p hp)
  have h := ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_piZero_eq_iff_homotopy _ _).mpr ⟨low⟩).symm.trans
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_piZero_eq_iff_homotopy _ _).mpr ⟨up⟩)
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_piZero_eq_iff_homotopy _ _).mp
  dsimp only [K, L, hc, hd, a] at h
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteKanProductNativeCone_kanLeg] at h
  change SSet.π₀.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex
      (finiteSiftedProductNativeKanLeg n p hp i ≫ (𝟙 _ :
        ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteKanProductDiagram n (fun i ↦ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.continuousKanObject (E i))).obj i).obj ⟶ _))) =
    SSet.π₀.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.finiteCommonFiberProductKanComparison n p ≫
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteSSetProjection n (fun i ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj (E i))
        i.as.down)) at h
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.finiteCommonFiberProductKanComparison_projection] at h
  simpa only [Category.comp_id] using h

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories
