module
public import SerrePositivity.KST.SConstruction.FixedBoundaryMappingSpace
public import SerrePositivity.KST.SConstruction.FamilyCompStructRealization

/-! # 元の全境界を固定する実円柱の合成
概要：元の二つの相対円柱を、同じ全境界を固定する実合成円柱にまとめる。
方針：固定境界写像空間内で実辺を合成し、同じ実三角形と全二面を保存する。
規約：境界で余分な null loop を許さず、全時刻の固定を実等号として保持する。
使われ方：前段までの累積補正を保持する全段 raw 比較の帰納段。
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

/-- 元の固定境界比較辺を戻すと、元の同じ全円柱の辺である。 -/
lemma fixedBoundaryMappingEdge_image {A T E : SSet.{u}} (j : A ⟶ T) (b : A ⟶ E)
    {f g : T ⟶ E} (hf : j ≫ f = b) (hg : j ≫ g = b) (H : SSet.Homotopy f g)
    (hr : (j ▷ (Δ[1] : SSet.{u})) ≫ H.h = fst A Δ[1] ≫ b) :
    ((fixedBoundaryMappingEdge j b hf hg H hr).map (fixedBoundaryMappingSpaceι j b)).edge =
      (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H)).edge := by
  apply SSet.yonedaEquiv.symm.injective
  rw [show SSet.yonedaEquiv.symm
      ((fixedBoundaryMappingEdge j b hf hg H hr).map (fixedBoundaryMappingSpaceι j b)).edge =
      SSet.yonedaEquiv.symm (fixedBoundaryMappingEdge j b hf hg H hr).edge ≫
        fixedBoundaryMappingSpaceι j b by rw [SSet.yonedaEquiv_symm_comp]; rfl]
  change SSet.yonedaEquiv.symm (SSet.yonedaEquiv (fixedBoundaryMappingPath j b H hr)) ≫ _ =
    SSet.yonedaEquiv.symm (SSet.yonedaEquiv (curry H.h))
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply, fixedBoundaryMappingPath_ι]

/-- 元の相対二円柱を両面に保持する実合成円柱と固定条件。 -/
structure FixedBoundaryCompositionData {A T E : SSet.{u}} (j : A ⟶ T) (b : A ⟶ E)
    {f g h : T ⟶ E} (H : SSet.Homotopy f g) (K : SSet.Homotopy g h) where
  /-- 同じ始点・終点を持つ実合成円柱。 -/
  homotopy : SSet.Homotopy f h
  /-- 元の全境界を全時刻で厳密に固定する。 -/
  relative : (j ▷ (Δ[1] : SSet.{u})) ≫ homotopy.h = fst A Δ[1] ≫ b
  /-- 元の二円柱と実合成円柱を全三面に保持する。 -/
  triangle : SSet.Edge.CompStruct
    (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H))
    (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy K))
    (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy homotopy))

/-- 元の二円柱を同じ全境界の中で実合成し、元の全三角形を保存する。 -/
def fixedBoundaryCompositionData {A T E : SSet.{u}} [KanComplex E]
    (j : A ⟶ T) [Mono j] (b : A ⟶ E) {f g h : T ⟶ E}
    (hf : j ≫ f = b) (hg : j ≫ g = b) (hh : j ≫ h = b)
    (H : SSet.Homotopy f g) (K : SSet.Homotopy g h)
    (hH : (j ▷ (Δ[1] : SSet.{u})) ≫ H.h = fst A Δ[1] ≫ b)
    (hK : (j ▷ (Δ[1] : SSet.{u})) ≫ K.h = fst A Δ[1] ≫ b) :
    FixedBoundaryCompositionData j b H K := by
  let d := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.kanMappingComposition (fixedBoundaryMappingEdge j b hf hg H hH)
    (fixedBoundaryMappingEdge j b hg hh K hK)
  let e := d.edge.map (fixedBoundaryMappingSpaceι j b)
  let V := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge e.toTruncated
  have he : (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy V)).edge = e.edge := by
    change SSet.yonedaEquiv (curry (uncurry (SSet.yonedaEquiv.symm e.edge))) = _
    rw [curry_uncurry, Equiv.apply_symm_apply]
  have hr : (j ▷ (Δ[1] : SSet.{u})) ≫ V.h = fst A Δ[1] ≫ b := by
    change (j ▷ (Δ[1] : SSet.{u})) ≫ uncurry (SSet.yonedaEquiv.symm e.edge) = _
    rw [← uncurry_pre_app]
    have hm : SSet.yonedaEquiv.symm e.edge =
        SSet.yonedaEquiv.symm d.edge.edge ≫ fixedBoundaryMappingSpaceι j b := by
      rw [SSet.yonedaEquiv_symm_comp]
      rfl
    rw [hm, Category.assoc, fixedBoundaryMappingSpaceι, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp,
      SSet.comp_const, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.uncurry_const_functorVertex]
  exact ⟨V, hr, (d.triangle.map (fixedBoundaryMappingSpaceι j b)).ofEq
    (fixedBoundaryMappingEdge_image j b hf hg H hH)
    (fixedBoundaryMappingEdge_image j b hg hh K hK) he.symm⟩

end SerrePositivity.KST.SConstruction
