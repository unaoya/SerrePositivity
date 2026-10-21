module

public import SerrePositivity.InfinityCategories.HomotopyLimits.SiftedCoherentProductNativeCone
public import SerrePositivity.InfinityCategories.F2.KanConeHomotopyTriangles
public import SerrePositivity.InfinityCategories.F2.HomotopyVerticalRestriction

/-!
概要：coherent な積の native な二脚を、元の射影変換の全空間作用へ照合する。
方針：全錐円柱の頂点辺と恒等図式辺を回収し、元の上下二単体を Kan ホモトピーへ戻す。
規約：元の Kan 比較・元の射影を保持。使われ方：native な積交換の射の同定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
variable {B : SSet.{u}} [IsSiftedInfinity B]
  (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})

/-- 全錐円柱の頂点辺は、元の積比較の coherent な辺の全一単体。 -/
lemma siftedCoherentProductNativeConeHomotopy_apexEdge :
    (F2.coneHomotopyApexEdge (siftedCoherentProductNativeConeHomotopy F G)).edge =
      (coherentNerveEdge (coherentProductTotalKanMap F G)).edge := by
  have h := F2.homotopyVertexEdge_prism (siftedCoherentProductNativeConeHomotopy F G)
    (joinInl _ _) (coherentProductComparisonApexPrism F G)
    (siftedCoherentProductNativeConeHomotopy_apex F G) (SSet.yonedaEquiv (𝟙 _))
  exact h.trans (SSet.yonedaEquiv_symm_app_id
    (coherentNerveEdge (coherentProductTotalKanMap F G)).edge)

/-- 全錐円柱の図式辺は、元の図式の値の恒等辺に定値。 -/
lemma siftedCoherentProductNativeConeHomotopy_diagramEdge (i : Discrete (ULift.{u} Bool)) :
    (F2.coneHomotopyDiagramEdge (siftedCoherentProductNativeConeHomotopy F G)
      (ULift.up (ComposableArrows.mk₀ i))).edge =
        (coherentNerveEdge
          (𝟙 ((kanBinaryDiagram (F2.coherentDiagramTotalKanObject F)
            (F2.coherentDiagramTotalKanObject G)).obj i))).edge := by
  have h := F2.homotopyVertexEdge_constant (siftedCoherentProductNativeConeHomotopy F G)
    (joinInr _ _) _ (siftedCoherentProductNativeConeHomotopy_diagram F G)
    (ULift.up (ComposableArrows.mk₀ i))
  change (F2.coneHomotopyDiagramEdge _ _).edge = _ at h
  have hv := (kanDiagramCoherentNerve_vertex
    (kanBinaryDiagram (F2.coherentDiagramTotalKanObject F)
      (F2.coherentDiagramTotalKanObject G)) i).trans
      (spaceInfinityVertex_eq_coherent _)
  exact h.trans ((congrArg (fun v ↦ PinchedHom.constant v 1) hv).trans
    (by rw [coherentNerveEdge_id, pinchedConstant_one]; rfl))

/-- 輸送した native な脚の、元の全空間 Kan 模型からの実際の Kan 射。 -/
def siftedCoherentProductNativeKanLeg (i : Discrete (ULift.{u} Bool)) :
    F2.coherentDiagramTotalKanObject (coherentSpaceTensorProduct F G) ⟶
      (kanBinaryDiagram (F2.coherentDiagramTotalKanObject F)
        (F2.coherentDiagramTotalKanObject G)).obj i :=
  F2.kanNativeConeLeg (siftedCoherentProductNativeCone F G) _
    ((siftedCoherentProductNativeCone_vertex F G).trans (spaceInfinityVertex_eq_coherent _)) i

/-- 元の native な脚は、元の積比較と元の直積射影の合成にホモトピック。 -/
lemma siftedCoherentProductNativeKanLeg_comparison (i : Discrete (ULift.{u} Bool)) :
    Nonempty (SSet.Homotopy (siftedCoherentProductNativeKanLeg F G i)
      (coherentProductTotalKanMap F G ≫
        (kanBinaryTensorCone (F2.coherentDiagramTotalKanObject F)
          (F2.coherentDiagramTotalKanObject G)).π.app i)) := by
  let K := F2.coherentDiagramTotalKanObject (coherentSpaceTensorProduct F G)
  let L := (kanTensorLeft (F2.coherentDiagramTotalKanObject F)).obj
    (F2.coherentDiagramTotalKanObject G)
  let hc := (siftedCoherentProductNativeCone_vertex F G).trans
    (spaceInfinityVertex_eq_coherent _)
  let hd := spaceBinaryTensorProductCone_vertex (F2.coherentDiagramTotalKanObject F)
    (F2.coherentDiagramTotalKanObject G)
  let a := coherentProductTotalKanMap F G
  let H := siftedCoherentProductNativeConeHomotopy F G
  let low := F2.kanConeHomotopyLower H K hc i (𝟙 _)
    (siftedCoherentProductNativeConeHomotopy_diagramEdge F G i)
  let up := F2.kanConeHomotopyUpper H K L hc hd i a
    (siftedCoherentProductNativeConeHomotopy_apexEdge F G)
  have h := ((functorVertex_piZero_eq_iff_homotopy _ _).mpr ⟨low⟩).symm.trans
    ((functorVertex_piZero_eq_iff_homotopy _ _).mpr ⟨up⟩)
  apply (functorVertex_piZero_eq_iff_homotopy _ _).mp
  dsimp only [K, L, hc, hd, a] at h
  rw [spaceBinaryTensorProductCone_kanLeg] at h
  change SSet.π₀.mk (functorVertex
      (siftedCoherentProductNativeKanLeg F G i ≫ (𝟙 _ :
        ((kanBinaryDiagram (F2.coherentDiagramTotalKanObject F)
          (F2.coherentDiagramTotalKanObject G)).obj i).obj ⟶ _))) =
    _ at h
  simpa only [Category.comp_id] using h

/-- 元の native な第一脚は、指定第一射影の全空間作用の Kan 置換にホモトピック。 -/
lemma siftedCoherentProductNativeKanLeg_left : Nonempty (SSet.Homotopy
    (siftedCoherentProductNativeKanLeg F G ⟨⟨true⟩⟩)
    (F2.continuousKanReplacement.map (coherentSpaceTensorProductTotalFst F G))) := by
  have h := siftedCoherentProductNativeKanLeg_comparison F G ⟨⟨true⟩⟩
  change Nonempty (SSet.Homotopy _ (coherentProductTotalKanComparison F G ≫
    fst (F2.coherentDiagramTotalKan F) (F2.coherentDiagramTotalKan G))) at h
  rwa [coherentProductTotalKanComparison_fst] at h

/-- 元の native な第二脚も、指定第二射影の全空間作用の Kan 置換にホモトピック。 -/
lemma siftedCoherentProductNativeKanLeg_right : Nonempty (SSet.Homotopy
    (siftedCoherentProductNativeKanLeg F G ⟨⟨false⟩⟩)
    (F2.continuousKanReplacement.map (coherentSpaceTensorProductTotalSnd F G))) := by
  have h := siftedCoherentProductNativeKanLeg_comparison F G ⟨⟨false⟩⟩
  change Nonempty (SSet.Homotopy _ (coherentProductTotalKanComparison F G ≫
    snd (F2.coherentDiagramTotalKan F) (F2.coherentDiagramTotalKan G))) at h
  rwa [coherentProductTotalKanComparison_snd] at h

end SerrePositivity.InfinityCategories.HomotopyLimits
