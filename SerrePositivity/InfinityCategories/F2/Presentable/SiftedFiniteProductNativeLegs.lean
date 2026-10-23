module

public import SerrePositivity.InfinityCategories.F2.Presentable.SiftedFiniteProductNativeCone
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.KanConeHomotopyTriangles
public import SerrePositivity.InfinityCategories.F2.CatInfinity.HomotopyVerticalRestriction
public import SerrePositivity.InfinityCategories.F1B.KanHomotopyClasses

/-!
概要：元の有限 fiber 積の全空間 Kan 模型の native 積錐の全脚。
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
variable (n : ℕ) {B : SSet.{u}} [IsSiftedInfinity B] {E : Fin (n + 1) → SSet.{u}}
  (p : (i : Fin (n + 1)) → E i ⟶ B) (hp : ∀ i, LeftFibration (p i))

/-- 元の全錐円柱の頂点辺は、元の全有限積比較と同じ全一単体。 -/
lemma finiteSiftedProductNativeConeHomotopy_apexEdge :
    (F2.coneHomotopyApexEdge (finiteSiftedProductNativeConeHomotopy n p hp)).edge =
      (coherentNerveEdge (finiteTotalComparisonKanMap n p)).edge := by
  have h := F2.homotopyVertexEdge_prism (finiteSiftedProductNativeConeHomotopy n p hp)
    (joinInl _ _) (finiteTotalComparisonApexPrism n p)
    (finiteSiftedProductNativeConeHomotopy_apex n p hp) (SSet.yonedaEquiv (𝟙 _))
  exact h.trans (SSet.yonedaEquiv_symm_app_id
    (coherentNerveEdge (finiteTotalComparisonKanMap n p)).edge)

/-- 全錐円柱の各底辺は、元の全空間 Kan 模型の恒等辺そのもの。 -/
lemma finiteSiftedProductNativeConeHomotopy_diagramEdge
    (i : Discrete (ULift.{u} (Fin (n + 1)))) :
    (F2.coneHomotopyDiagramEdge (finiteSiftedProductNativeConeHomotopy n p hp)
      (ULift.up (ComposableArrows.mk₀ i))).edge =
        (coherentNerveEdge
          (𝟙 ((finiteKanProductDiagram n (fun i ↦ F2.continuousKanObject (E i))).obj i))).edge := by
  have h := F2.homotopyVertexEdge_constant (finiteSiftedProductNativeConeHomotopy n p hp)
    (joinInr _ _) _ (finiteSiftedProductNativeConeHomotopy_diagram n p hp)
    (ULift.up (ComposableArrows.mk₀ i))
  change (F2.coneHomotopyDiagramEdge _ _).edge = _ at h
  have hv := (kanDiagramCoherentNerve_vertex
    (finiteKanProductDiagram n (fun i ↦ F2.continuousKanObject (E i))) i).trans
      (spaceInfinityVertex_eq_coherent _)
  exact h.trans ((congrArg (fun v ↦ PinchedHom.constant v 1) hv).trans
    (by rw [coherentNerveEdge_id, pinchedConstant_one]; rfl))

/-- 元の native 積錐の各脚を、元の全空間 Kan 対象からの射として読み戻す。 -/
def finiteSiftedProductNativeKanLeg (i : Discrete (ULift.{u} (Fin (n + 1)))) :
    F2.continuousKanObject (finiteCommonFiberProduct n p) ⟶
      (finiteKanProductDiagram n (fun i ↦ F2.continuousKanObject (E i))).obj i :=
  F2.kanNativeConeLeg (finiteSiftedProductNativeCone n p hp) _
    (finiteSiftedProductNativeCone_vertex n p hp) i

/-- 元の全 native 脚は、それぞれ元の共通 fiber 積射影の Kan 像にホモトピック。 -/
lemma finiteSiftedProductNativeKanLeg_projection
    (i : Discrete (ULift.{u} (Fin (n + 1)))) :
    Nonempty (SSet.Homotopy (finiteSiftedProductNativeKanLeg n p hp i)
      (F2.continuousKanReplacement.map (finiteCommonFiberProductProjection n p i.as.down))) := by
  let K := F2.continuousKanObject (finiteCommonFiberProduct n p)
  let L := finiteKanProductObject n (fun i ↦ F2.continuousKanObject (E i))
  let hc := finiteSiftedProductNativeCone_vertex n p hp
  let hd := finiteKanProductNativeCone_vertex n (fun i ↦ F2.continuousKanObject (E i))
  let a := finiteTotalComparisonKanMap n p
  let H := finiteSiftedProductNativeConeHomotopy n p hp
  let low := F2.kanConeHomotopyLower H K hc i (𝟙 _)
    (finiteSiftedProductNativeConeHomotopy_diagramEdge n p hp i)
  let up := F2.kanConeHomotopyUpper H K L hc hd i a
    (finiteSiftedProductNativeConeHomotopy_apexEdge n p hp)
  have h := ((functorVertex_piZero_eq_iff_homotopy _ _).mpr ⟨low⟩).symm.trans
    ((functorVertex_piZero_eq_iff_homotopy _ _).mpr ⟨up⟩)
  apply (functorVertex_piZero_eq_iff_homotopy _ _).mp
  dsimp only [K, L, hc, hd, a] at h
  rw [finiteKanProductNativeCone_kanLeg] at h
  change SSet.π₀.mk (functorVertex
      (finiteSiftedProductNativeKanLeg n p hp i ≫ (𝟙 _ :
        ((finiteKanProductDiagram n (fun i ↦ F2.continuousKanObject (E i))).obj i).obj ⟶ _))) =
    SSet.π₀.mk (functorVertex (finiteCommonFiberProductKanComparison n p ≫
      nonemptyFiniteSSetProjection n (fun i ↦ F2.continuousKanReplacement.obj (E i))
        i.as.down)) at h
  rw [finiteCommonFiberProductKanComparison_projection] at h
  simpa only [Category.comp_id] using h

end SerrePositivity.InfinityCategories.HomotopyLimits
