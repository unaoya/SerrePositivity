module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SiftedCoherentProductNativeCone
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanConeHomotopyTriangles
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.HomotopyVerticalRestriction

/-!
概要：coherent な積の native な二脚を、元の射影変換の全空間作用へ照合する。
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
variable {B : SSet.{u}} [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.IsSiftedInfinity B]
  (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})

/-- 全錐円柱の頂点辺は、元の積比較の coherent な辺の全一単体。 -/
lemma siftedCoherentProductNativeConeHomotopy_apexEdge :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneHomotopyApexEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.siftedCoherentProductNativeConeHomotopy F G)).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.coherentProductTotalKanMap F G)).edge := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.homotopyVertexEdge_prism (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.siftedCoherentProductNativeConeHomotopy F G)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl _ _) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.coherentProductComparisonApexPrism F G)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.siftedCoherentProductNativeConeHomotopy_apex F G) (SSet.yonedaEquiv (𝟙 _))
  exact h.trans (SSet.yonedaEquiv_symm_app_id
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.coherentProductTotalKanMap F G)).edge)

/-- 全錐円柱の図式辺は、元の図式の値の恒等辺に定値。 -/
lemma siftedCoherentProductNativeConeHomotopy_diagramEdge (i : Discrete (ULift.{u} Bool)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneHomotopyDiagramEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.siftedCoherentProductNativeConeHomotopy F G)
      (ULift.up (ComposableArrows.mk₀ i))).edge =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge
          (𝟙 ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanBinaryDiagram (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalKanObject F)
            (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalKanObject G)).obj i))).edge := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.homotopyVertexEdge_constant (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.siftedCoherentProductNativeConeHomotopy F G)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr _ _) _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.siftedCoherentProductNativeConeHomotopy_diagram F G)
    (ULift.up (ComposableArrows.mk₀ i))
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneHomotopyDiagramEdge _ _).edge = _ at h
  have hv := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve_vertex
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanBinaryDiagram (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalKanObject F)
      (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalKanObject G)) i).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityVertex_eq_coherent _)
  exact h.trans ((congrArg (fun v ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant v 1) hv).trans
    (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge_id, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one]; rfl))

/-- 輸送した native な脚の、元の全空間 Kan 模型からの実際の Kan 射。 -/
def siftedCoherentProductNativeKanLeg (i : Discrete (ULift.{u} Bool)) :
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalKanObject (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentSpaceTensorProduct F G) ⟶
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanBinaryDiagram (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalKanObject F)
        (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalKanObject G)).obj i :=
  _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.kanNativeConeLeg (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.siftedCoherentProductNativeCone F G) _
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.siftedCoherentProductNativeCone_vertex F G).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityVertex_eq_coherent _)) i

/-- 元の native な脚は、元の積比較と元の直積射影の合成にホモトピック。 -/
lemma siftedCoherentProductNativeKanLeg_comparison (i : Discrete (ULift.{u} Bool)) :
    Nonempty (SSet.Homotopy (siftedCoherentProductNativeKanLeg F G i)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.coherentProductTotalKanMap F G ≫
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanBinaryTensorCone (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalKanObject F)
          (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalKanObject G)).π.app i)) := by
  let K := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalKanObject (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentSpaceTensorProduct F G)
  let L := (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanTensorLeft (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalKanObject F)).obj
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalKanObject G)
  let hc := (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.siftedCoherentProductNativeCone_vertex F G).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityVertex_eq_coherent _)
  let hd := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.spaceBinaryTensorProductCone_vertex (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalKanObject F)
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalKanObject G)
  let a := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.coherentProductTotalKanMap F G
  let H := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.siftedCoherentProductNativeConeHomotopy F G
  let low := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.kanConeHomotopyLower H K hc i (𝟙 _)
    (siftedCoherentProductNativeConeHomotopy_diagramEdge F G i)
  let up := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.kanConeHomotopyUpper H K L hc hd i a
    (siftedCoherentProductNativeConeHomotopy_apexEdge F G)
  have h := ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_piZero_eq_iff_homotopy _ _).mpr ⟨low⟩).symm.trans
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_piZero_eq_iff_homotopy _ _).mpr ⟨up⟩)
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_piZero_eq_iff_homotopy _ _).mp
  dsimp only [K, L, hc, hd, a] at h
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.spaceBinaryTensorProductCone_kanLeg] at h
  change SSet.π₀.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex
      (siftedCoherentProductNativeKanLeg F G i ≫ (𝟙 _ :
        ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanBinaryDiagram (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalKanObject F)
          (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalKanObject G)).obj i).obj ⟶ _))) =
    _ at h
  simpa only [Category.comp_id] using h

/-- 元の native な第一脚は、指定第一射影の全空間作用の Kan 置換にホモトピック。 -/
lemma siftedCoherentProductNativeKanLeg_left : Nonempty (SSet.Homotopy
    (siftedCoherentProductNativeKanLeg F G ⟨⟨true⟩⟩)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentSpaceTensorProductTotalFst F G))) := by
  have h := siftedCoherentProductNativeKanLeg_comparison F G ⟨⟨true⟩⟩
  change Nonempty (SSet.Homotopy _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.coherentProductTotalKanComparison F G ≫
    fst (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalKan F) (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalKan G))) at h
  rwa [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.coherentProductTotalKanComparison_fst] at h

/-- 元の native な第二脚も、指定第二射影の全空間作用の Kan 置換にホモトピック。 -/
lemma siftedCoherentProductNativeKanLeg_right : Nonempty (SSet.Homotopy
    (siftedCoherentProductNativeKanLeg F G ⟨⟨false⟩⟩)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentSpaceTensorProductTotalSnd F G))) := by
  have h := siftedCoherentProductNativeKanLeg_comparison F G ⟨⟨false⟩⟩
  change Nonempty (SSet.Homotopy _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.coherentProductTotalKanComparison F G ≫
    snd (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalKan F) (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalKan G))) at h
  rwa [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.coherentProductTotalKanComparison_snd] at h

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories
