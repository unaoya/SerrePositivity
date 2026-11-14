module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SiftedProductNativeCone
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.KanConeHomotopyTriangles
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.HomotopyVerticalRestriction

/-!
概要：sifted な積の native な二脚を、元の全空間の二射影へ照合する。
方針：全錐円柱の頂点辺と恒等図式辺を回収し、元の上下二単体を Kan ホモトピーへ戻す。
規約：元の Kan 比較・元の射影を保持。使われ方：native な積交換の射の同定。

対応節は Kerodon 9.7（Tag 06ZD）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories
variable {E D B : SSet.{u}} [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.IsSiftedInfinity B]
  (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (q : D ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q]

/-- 全錐円柱の頂点辺は、元の積比較の coherent な辺の全一単体。 -/
lemma siftedProductNativeConeHomotopy_apexEdge :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneHomotopyApexEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.siftedProductNativeConeHomotopy p q)).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.totalProductComparisonKanMap p q)).edge := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.homotopyVertexEdge_prism (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.siftedProductNativeConeHomotopy p q)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl _ _) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.totalProductComparisonApexPrism p q)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.siftedProductNativeConeHomotopy_apex p q) (SSet.yonedaEquiv (𝟙 _))
  exact h.trans (SSet.yonedaEquiv_symm_app_id
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.totalProductComparisonKanMap p q)).edge)

/-- 全錐円柱の図式辺は、元の図式の値の恒等辺に定値。 -/
lemma siftedProductNativeConeHomotopy_diagramEdge (i : Discrete (ULift.{u} Bool)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneHomotopyDiagramEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.siftedProductNativeConeHomotopy p q)
      (ULift.up (ComposableArrows.mk₀ i))).edge =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge
          (𝟙 ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanBinaryDiagram (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.continuousKanObject E)
            (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.continuousKanObject D)).obj i))).edge := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.homotopyVertexEdge_constant (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.siftedProductNativeConeHomotopy p q)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr _ _) _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.siftedProductNativeConeHomotopy_diagram p q)
    (ULift.up (ComposableArrows.mk₀ i))
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneHomotopyDiagramEdge _ _).edge = _ at h
  have hv := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve_vertex
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanBinaryDiagram (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.continuousKanObject E) (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.continuousKanObject D)) i).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityVertex_eq_coherent _)
  exact h.trans ((congrArg (fun v ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant v 1) hv).trans
    (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge_id, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one]; rfl))

/-- 輸送した native な脚の、元の全空間 Kan 模型からの実際の Kan 射。 -/
def siftedProductNativeKanLeg (i : Discrete (ULift.{u} Bool)) :
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.continuousKanObject (pullback p q) ⟶
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanBinaryDiagram (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.continuousKanObject E) (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.continuousKanObject D)).obj i :=
  _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.kanNativeConeLeg (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.siftedProductNativeCone p q) _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.siftedProductNativeCone_vertex p q) i

/-- 元の native な脚は、元の積比較と元の直積射影の合成にホモトピック。 -/
lemma siftedProductNativeKanLeg_comparison (i : Discrete (ULift.{u} Bool)) :
    Nonempty (SSet.Homotopy (siftedProductNativeKanLeg p q i)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.totalProductComparisonKanMap p q ≫
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanBinaryTensorCone (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.continuousKanObject E) (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.continuousKanObject D)).π.app i)) := by
  let K := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.continuousKanObject (pullback p q)
  let L := (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanTensorLeft (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.continuousKanObject E)).obj (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.continuousKanObject D)
  let hc := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.siftedProductNativeCone_vertex p q
  let hd := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.spaceBinaryTensorProductCone_vertex (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.continuousKanObject E)
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.continuousKanObject D)
  let a := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.totalProductComparisonKanMap p q
  let H := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.siftedProductNativeConeHomotopy p q
  let low := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.kanConeHomotopyLower H K hc i (𝟙 _)
    (siftedProductNativeConeHomotopy_diagramEdge p q i)
  let up := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.kanConeHomotopyUpper H K L hc hd i a
    (siftedProductNativeConeHomotopy_apexEdge p q)
  have h := ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_piZero_eq_iff_homotopy _ _).mpr ⟨low⟩).symm.trans
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_piZero_eq_iff_homotopy _ _).mpr ⟨up⟩)
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_piZero_eq_iff_homotopy _ _).mp
  dsimp only [K, L, hc, hd, a] at h
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.spaceBinaryTensorProductCone_kanLeg] at h
  change SSet.π₀.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex
      (siftedProductNativeKanLeg p q i ≫ (𝟙 _ :
        ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanBinaryDiagram (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.continuousKanObject E)
          (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.continuousKanObject D)).obj i).obj ⟶ _))) =
    _ at h
  simpa only [Category.comp_id] using h

/-- 元の native な第一脚は、元の第一全空間射影の Kan 置換にホモトピック。 -/
lemma siftedProductNativeKanLeg_left : Nonempty (SSet.Homotopy
    (siftedProductNativeKanLeg p q ⟨⟨true⟩⟩)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map (pullback.fst p q))) := by
  have h := siftedProductNativeKanLeg_comparison p q ⟨⟨true⟩⟩
  change Nonempty (SSet.Homotopy _ (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.totalKanProductComparison p q ≫
    fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj E) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj D))) at h
  rwa [_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.totalKanProductComparison, lift_fst] at h

/-- 元の native な第二脚は、元の第二全空間射影の Kan 置換にホモトピック。 -/
lemma siftedProductNativeKanLeg_right : Nonempty (SSet.Homotopy
    (siftedProductNativeKanLeg p q ⟨⟨false⟩⟩)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map (pullback.snd p q))) := by
  have h := siftedProductNativeKanLeg_comparison p q ⟨⟨false⟩⟩
  change Nonempty (SSet.Homotopy _ (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.totalKanProductComparison p q ≫
    snd (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj E) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj D))) at h
  rwa [_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.totalKanProductComparison, lift_snd] at h

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories
