module

public import SerrePositivity.InfinityCategories.HomotopyLimits.SiftedProductNativeCone
public import SerrePositivity.InfinityCategories.F2.KanConeHomotopyTriangles
public import SerrePositivity.InfinityCategories.F2.HomotopyVerticalRestriction

/-!
概要：sifted な積の native な二脚を、元の全空間の二射影へ照合する。
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
variable {E D B : SSet.{u}} [IsSiftedInfinity B]
  (p : E ⟶ B) [LeftFibration p] (q : D ⟶ B) [LeftFibration q]

/-- 全錐円柱の頂点辺は、元の積比較の coherent な辺の全一単体。 -/
lemma siftedProductNativeConeHomotopy_apexEdge :
    (F2.coneHomotopyApexEdge (siftedProductNativeConeHomotopy p q)).edge =
      (coherentNerveEdge (totalProductComparisonKanMap p q)).edge := by
  have h := F2.homotopyVertexEdge_prism (siftedProductNativeConeHomotopy p q)
    (joinInl _ _) (totalProductComparisonApexPrism p q)
    (siftedProductNativeConeHomotopy_apex p q) (SSet.yonedaEquiv (𝟙 _))
  exact h.trans (SSet.yonedaEquiv_symm_app_id
    (coherentNerveEdge (totalProductComparisonKanMap p q)).edge)

/-- 全錐円柱の図式辺は、元の図式の値の恒等辺に定値。 -/
lemma siftedProductNativeConeHomotopy_diagramEdge (i : Discrete (ULift.{u} Bool)) :
    (F2.coneHomotopyDiagramEdge (siftedProductNativeConeHomotopy p q)
      (ULift.up (ComposableArrows.mk₀ i))).edge =
        (coherentNerveEdge
          (𝟙 ((kanBinaryDiagram (F2.continuousKanObject E)
            (F2.continuousKanObject D)).obj i))).edge := by
  have h := F2.homotopyVertexEdge_constant (siftedProductNativeConeHomotopy p q)
    (joinInr _ _) _ (siftedProductNativeConeHomotopy_diagram p q)
    (ULift.up (ComposableArrows.mk₀ i))
  change (F2.coneHomotopyDiagramEdge _ _).edge = _ at h
  have hv := (kanDiagramCoherentNerve_vertex
    (kanBinaryDiagram (F2.continuousKanObject E) (F2.continuousKanObject D)) i).trans
      (spaceInfinityVertex_eq_coherent _)
  exact h.trans ((congrArg (fun v ↦ PinchedHom.constant v 1) hv).trans
    (by rw [coherentNerveEdge_id, pinchedConstant_one]; rfl))

/-- 輸送した native な脚の、元の全空間 Kan 模型からの実際の Kan 射。 -/
def siftedProductNativeKanLeg (i : Discrete (ULift.{u} Bool)) :
    F2.continuousKanObject (pullback p q) ⟶
      (kanBinaryDiagram (F2.continuousKanObject E) (F2.continuousKanObject D)).obj i :=
  F2.kanNativeConeLeg (siftedProductNativeCone p q) _ (siftedProductNativeCone_vertex p q) i

/-- 元の native な脚は、元の積比較と元の直積射影の合成にホモトピック。 -/
lemma siftedProductNativeKanLeg_comparison (i : Discrete (ULift.{u} Bool)) :
    Nonempty (SSet.Homotopy (siftedProductNativeKanLeg p q i)
      (totalProductComparisonKanMap p q ≫
        (kanBinaryTensorCone (F2.continuousKanObject E) (F2.continuousKanObject D)).π.app i)) := by
  let K := F2.continuousKanObject (pullback p q)
  let L := (kanTensorLeft (F2.continuousKanObject E)).obj (F2.continuousKanObject D)
  let hc := siftedProductNativeCone_vertex p q
  let hd := spaceBinaryTensorProductCone_vertex (F2.continuousKanObject E)
    (F2.continuousKanObject D)
  let a := totalProductComparisonKanMap p q
  let H := siftedProductNativeConeHomotopy p q
  let low := F2.kanConeHomotopyLower H K hc i (𝟙 _)
    (siftedProductNativeConeHomotopy_diagramEdge p q i)
  let up := F2.kanConeHomotopyUpper H K L hc hd i a
    (siftedProductNativeConeHomotopy_apexEdge p q)
  have h := ((functorVertex_piZero_eq_iff_homotopy _ _).mpr ⟨low⟩).symm.trans
    ((functorVertex_piZero_eq_iff_homotopy _ _).mpr ⟨up⟩)
  apply (functorVertex_piZero_eq_iff_homotopy _ _).mp
  dsimp only [K, L, hc, hd, a] at h
  rw [spaceBinaryTensorProductCone_kanLeg] at h
  change SSet.π₀.mk (functorVertex
      (siftedProductNativeKanLeg p q i ≫ (𝟙 _ :
        ((kanBinaryDiagram (F2.continuousKanObject E)
          (F2.continuousKanObject D)).obj i).obj ⟶ _))) =
    _ at h
  simpa only [Category.comp_id] using h

/-- 元の native な第一脚は、元の第一全空間射影の Kan 置換にホモトピック。 -/
lemma siftedProductNativeKanLeg_left : Nonempty (SSet.Homotopy
    (siftedProductNativeKanLeg p q ⟨⟨true⟩⟩)
    (F2.continuousKanReplacement.map (pullback.fst p q))) := by
  have h := siftedProductNativeKanLeg_comparison p q ⟨⟨true⟩⟩
  change Nonempty (SSet.Homotopy _ (F2.totalKanProductComparison p q ≫
    fst (F2.continuousKanReplacement.obj E) (F2.continuousKanReplacement.obj D))) at h
  rwa [F2.totalKanProductComparison, lift_fst] at h

/-- 元の native な第二脚は、元の第二全空間射影の Kan 置換にホモトピック。 -/
lemma siftedProductNativeKanLeg_right : Nonempty (SSet.Homotopy
    (siftedProductNativeKanLeg p q ⟨⟨false⟩⟩)
    (F2.continuousKanReplacement.map (pullback.snd p q))) := by
  have h := siftedProductNativeKanLeg_comparison p q ⟨⟨false⟩⟩
  change Nonempty (SSet.Homotopy _ (F2.totalKanProductComparison p q ≫
    snd (F2.continuousKanReplacement.obj E) (F2.continuousKanReplacement.obj D))) at h
  rwa [F2.totalKanProductComparison, lift_snd] at h

end SerrePositivity.InfinityCategories.HomotopyLimits
