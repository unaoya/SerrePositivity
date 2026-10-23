module

public import SerrePositivity.InfinityCategories.HomotopyLimits.FiniteCoherentProductNativeCone
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.KanConeHomotopyTriangles
public import SerrePositivity.InfinityCategories.F2.CatInfinity.HomotopyVerticalRestriction
public import SerrePositivity.InfinityCategories.F1B.KanHomotopyClasses

/-!
概要：元の有限 coherent 積図式の余極限 Kan 模型の native 積錐の全脚。
方針：同じ全錐円柱の両三角形から、全 native 脚を元の射影の Kan 像と照合する。
規約：全因子について元の一単体とホモトピーを保持する。
使われ方：P_Σ の sifted 余極限閉性の全有限積比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
variable (n : ℕ) {B : SSet.{u}} [IsSiftedInfinity B]
  (F : Fin (n + 1) → ((SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}))

/-- 元の全錐円柱の頂点辺は、元の全有限積比較と同じ全一単体。 -/
lemma finiteSiftedCoherentProductNativeConeHomotopy_apexEdge :
    (F2.coneHomotopyApexEdge (finiteSiftedCoherentProductNativeConeHomotopy n F)).edge =
      (coherentNerveEdge (finiteCoherentTotalComparisonKanMap n F)).edge := by
  have h := F2.homotopyVertexEdge_prism (finiteSiftedCoherentProductNativeConeHomotopy n F)
    (joinInl _ _) (finiteCoherentTotalComparisonApexPrism n F)
    (finiteSiftedCoherentProductNativeConeHomotopy_apex n F) (SSet.yonedaEquiv (𝟙 _))
  exact h.trans (SSet.yonedaEquiv_symm_app_id
    (coherentNerveEdge (finiteCoherentTotalComparisonKanMap n F)).edge)

/-- 全錐円柱の各底辺は、元の全空間 Kan 模型の恒等辺そのもの。 -/
lemma finiteSiftedCoherentProductNativeConeHomotopy_diagramEdge
    (i : Discrete (ULift.{u} (Fin (n + 1)))) :
    (F2.coneHomotopyDiagramEdge (finiteSiftedCoherentProductNativeConeHomotopy n F)
      (ULift.up (ComposableArrows.mk₀ i))).edge =
        (coherentNerveEdge
          (𝟙 ((finiteKanProductDiagram n
            (fun i ↦ F2.coherentDiagramTotalKanObject (F i))).obj i))).edge := by
  have h := F2.homotopyVertexEdge_constant (finiteSiftedCoherentProductNativeConeHomotopy n F)
    (joinInr _ _) _ (finiteSiftedCoherentProductNativeConeHomotopy_diagram n F)
    (ULift.up (ComposableArrows.mk₀ i))
  change (F2.coneHomotopyDiagramEdge _ _).edge = _ at h
  have hv := (kanDiagramCoherentNerve_vertex
    (finiteKanProductDiagram n (fun i ↦ F2.coherentDiagramTotalKanObject (F i))) i).trans
      (spaceInfinityVertex_eq_coherent _)
  exact h.trans ((congrArg (fun v ↦ PinchedHom.constant v 1) hv).trans
    (by rw [coherentNerveEdge_id, pinchedConstant_one]; rfl))

/-- 元の native 積錐の各脚を、元の全空間 Kan 対象からの射として読み戻す。 -/
def finiteSiftedCoherentProductNativeKanLeg (i : Discrete (ULift.{u} (Fin (n + 1)))) :
    F2.coherentDiagramTotalKanObject (finiteCoherentSpaceProduct n F) ⟶
      (finiteKanProductDiagram n (fun i ↦ F2.coherentDiagramTotalKanObject (F i))).obj i :=
  F2.kanNativeConeLeg (finiteSiftedCoherentProductNativeCone n F) _
    (finiteSiftedCoherentProductNativeCone_vertex n F) i

/-- 元の全 native 脚は、それぞれ元の反復射影の全空間作用の Kan 像にホモトピック。 -/
lemma finiteSiftedCoherentProductNativeKanLeg_projection
    (i : Discrete (ULift.{u} (Fin (n + 1)))) :
    Nonempty (SSet.Homotopy (finiteSiftedCoherentProductNativeKanLeg n F i)
      (F2.continuousKanReplacement.map
        (finiteCoherentSpaceProductTotalProjection n F i.as.down))) := by
  let K := F2.coherentDiagramTotalKanObject (finiteCoherentSpaceProduct n F)
  let L := finiteKanProductObject n (fun i ↦ F2.coherentDiagramTotalKanObject (F i))
  let hc := finiteSiftedCoherentProductNativeCone_vertex n F
  let hd := finiteKanProductNativeCone_vertex n (fun i ↦ F2.coherentDiagramTotalKanObject (F i))
  let a := finiteCoherentTotalComparisonKanMap n F
  let H := finiteSiftedCoherentProductNativeConeHomotopy n F
  let low := F2.kanConeHomotopyLower H K hc i (𝟙 _)
    (finiteSiftedCoherentProductNativeConeHomotopy_diagramEdge n F i)
  let up := F2.kanConeHomotopyUpper H K L hc hd i a
    (finiteSiftedCoherentProductNativeConeHomotopy_apexEdge n F)
  have h := ((functorVertex_piZero_eq_iff_homotopy _ _).mpr ⟨low⟩).symm.trans
    ((functorVertex_piZero_eq_iff_homotopy _ _).mpr ⟨up⟩)
  apply (functorVertex_piZero_eq_iff_homotopy _ _).mp
  dsimp only [K, L, hc, hd, a] at h
  rw [finiteKanProductNativeCone_kanLeg] at h
  change SSet.π₀.mk (functorVertex
      (finiteSiftedCoherentProductNativeKanLeg n F i ≫ (𝟙 _ :
        ((finiteKanProductDiagram n
          (fun i ↦ F2.coherentDiagramTotalKanObject (F i))).obj i).obj ⟶ _))) =
    SSet.π₀.mk (functorVertex (finiteCoherentProductTotalKanComparison n F ≫
      nonemptyFiniteSSetProjection n (fun i ↦ F2.coherentDiagramTotalKan (F i))
        i.as.down)) at h
  rw [finiteCoherentProductTotalKanComparison_projection] at h
  simpa only [Category.comp_id] using h

end SerrePositivity.InfinityCategories.HomotopyLimits
