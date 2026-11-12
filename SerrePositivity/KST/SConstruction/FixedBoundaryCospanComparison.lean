module
public import SerrePositivity.KST.SConstruction.FixedBoundaryHomotopyComposition
public import SerrePositivity.KST.SConstruction.KanCospanPastingChoices

/-! # 共通終点を持つ元の二円柱の境界固定実比較
概要：共通終点への二つの元の円柱を保持し、両始点間の実比較円柱を全境界固定で構成する。
方針：全境界を固定する Kan 写像空間内で同じ外側ホーンを充填し、元の両脚を面に保つ。
規約：全円柱と全境界の厳密な固定式を保存し、類だけの比較で終えない。
使われ方：元の BF 比較辺と復号辺を結ぶ二円柱を、一つの直接比較円柱へまとめる。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 共通終点への元の二円柱を全体として二面に持つ、境界固定の直接比較データ。 -/
structure FixedBoundaryCospanData {A T E : SSet.{u}} (j : A ⟶ T) (b : A ⟶ E)
    {f g h : T ⟶ E} (H : SSet.Homotopy f h) (K : SSet.Homotopy g h) where
  /-- 元の両始点間の実比較円柱。 -/
  homotopy : SSet.Homotopy f g
  /-- 全境界は全比較時刻で厳密に固定。 -/
  relative : (j ▷ (Δ[1] : SSet.{u})) ≫ homotopy.h = fst A Δ[1] ≫ b
  /-- 元の二円柱と直接比較円柱を全三面に持つ実二単体。 -/
  triangle : SSet.Edge.CompStruct
    (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy homotopy))
    (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy K))
    (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H))
  /-- 元の二円柱を持つ全三角形も、全パラメータで元の全境界を固定する。 -/
  triangle_relative : (j ▷ (Δ[2] : SSet.{u})) ≫ familyCompStructRealization triangle =
    fst A Δ[2] ≫ b

/-- 元の共通終点への二脚を保ち、全境界を固定する実比較円柱と全三角形を得る。 -/
def fixedBoundaryCospanData {A T E : SSet.{u}} [KanComplex E]
    (j : A ⟶ T) [Mono j] (b : A ⟶ E) {f g h : T ⟶ E}
    (hf : j ≫ f = b) (hg : j ≫ g = b) (hh : j ≫ h = b)
    (H : SSet.Homotopy f h) (K : SSet.Homotopy g h)
    (hH : (j ▷ (Δ[1] : SSet.{u})) ≫ H.h = fst A Δ[1] ≫ b)
    (hK : (j ▷ (Δ[1] : SSet.{u})) ≫ K.h = fst A Δ[1] ≫ b) :
    FixedBoundaryCospanData j b H K := by
  let a := fixedBoundaryMappingEdge j b hf hh H hH
  let c := fixedBoundaryMappingEdge j b hg hh K hK
  let v := (kanCospanPastingChoices_isContractibleKan a c).nonempty.some
  let d := kanCospanPastedEdge a c v
  let e := d.map (fixedBoundaryMappingSpaceι j b)
  let V := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge e.toTruncated
  have he : (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy V)).edge = e.edge := by
    change SSet.yonedaEquiv (curry (uncurry (SSet.yonedaEquiv.symm e.edge))) = _
    rw [curry_uncurry, Equiv.apply_symm_apply]
  have hr : (j ▷ (Δ[1] : SSet.{u})) ≫ V.h = fst A Δ[1] ≫ b := by
    change (j ▷ (Δ[1] : SSet.{u})) ≫ uncurry (SSet.yonedaEquiv.symm e.edge) = _
    rw [← uncurry_pre_app]
    have hm : SSet.yonedaEquiv.symm e.edge =
        SSet.yonedaEquiv.symm d.edge ≫ fixedBoundaryMappingSpaceι j b := by
      rw [SSet.yonedaEquiv_symm_comp]
      rfl
    rw [hm, Category.assoc, fixedBoundaryMappingSpaceι, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp,
      SSet.comp_const, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.uncurry_const_functorVertex]
  let t := ((kanCospanPastedTriangle a c v).map
    (fixedBoundaryMappingSpaceι j b)).ofEq he.symm
      (fixedBoundaryMappingEdge_image j b hg hh K hK)
      (fixedBoundaryMappingEdge_image j b hf hh H hH)
  have ht : (j ▷ (Δ[2] : SSet.{u})) ≫ familyCompStructRealization t = fst A Δ[2] ≫ b := by
    change (j ▷ (Δ[2] : SSet.{u})) ≫ uncurry (SSet.yonedaEquiv.symm t.simplex) = _
    rw [← uncurry_pre_app]
    have hm : SSet.yonedaEquiv.symm t.simplex =
        SSet.yonedaEquiv.symm (kanCospanPastedTriangle a c v).simplex ≫
          fixedBoundaryMappingSpaceι j b := by
      rw [SSet.yonedaEquiv_symm_comp]
      rfl
    rw [hm, Category.assoc, fixedBoundaryMappingSpaceι, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp,
      SSet.comp_const, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.uncurry_const_functorVertex]
  exact ⟨V, hr, t, ht⟩

end SerrePositivity.KST.SConstruction
