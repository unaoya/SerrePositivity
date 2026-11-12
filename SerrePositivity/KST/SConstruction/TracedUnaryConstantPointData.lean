module
public import SerrePositivity.KST.SConstruction.FamilyChainCompositeDataMap
public import SerrePositivity.KST.SConstruction.TracedCompositePointTraces
public import SerrePositivity.KST.SConstruction.TracedBFStageVertices

/-! # 元の単一射補正の全木を同じ定数端点の一点円柱へ移す
概要：元の単一射補正を直通列点へ制限し、同じ両段頂点を定数族として回収する。
方針：元の全証人の前合成と端点表示移送を用い、全区間と全三角形を保持する。
規約：元の全円柱・全木を選び直さず、同じ全 trace の順序を保持する。
使われ方：合成補正の二部分を元の単一射円柱で構成する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet Spectra Spectra.PointedMapping
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable {I : Type u} [SmallCategory I] (F : I ⥤ StableModel.{u}) {x y : I} (f : x ⟶ y)

/-- 元の単一射の始点を直通列点へ制限しても、元の段射の同じ定数族。 -/
lemma monicKPrismRawLevel_point (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (coherentArrowStringDirect f) ≫ monicKPrismRawLevelFamily n F f =
      SSet.const (familyVertex (monicKToRawLevelMap (F.map f) n)) := by
  rw [monicKPrismRawLevelFamily, SSet.comp_const]

/-- 元の補正済み段の一点制限は、同じ raw 段頂点の定数族。 -/
lemma monicKPrismTracedStage_point_const (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (coherentArrowStringDirect f) ≫ (monicKPrismTracedStage F f n).val =
      SSet.const (monicKTracedRawStageVertex F f n) := by
  rw [← SSet.yonedaEquiv_symm_zero]
  apply SSet.yonedaEquiv.injective
  simpa only [Equiv.apply_symm_apply] using monicKPrismTracedStage_point_vertex F f n

/-- 元の単一射の全木を一点へ写し、同じ両端を定数頂点族で表示したデータ。 -/
def monicKPrismUnaryConstantPointData (n : ℕ) :=
  ((monicKPrismUnaryCorrectionData F f n).precomp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (coherentArrowStringDirect f))).endpointTransport
      (monicKPrismRawLevel_point F f n).symm (monicKPrismTracedStage_point_const F f n)

/-- 同じ全円柱の直通列制限を、表示移送後も厳密に保持する。 -/
lemma monicKPrismUnaryConstantPointData_h (n : ℕ) :
    (monicKPrismUnaryConstantPointData F f n).homotopy.h =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (coherentArrowStringDirect f) ▷ (Δ[1] : SSet.{u})) ≫
        (monicKPrismUnaryCorrectionData F f n).homotopy.h := by
  rw [monicKPrismUnaryConstantPointData, FamilyChainCompositeData.endpointTransport_h,
    FamilyChainCompositeData.precomp_h]

/-- 元の単一射の同じ全区間を同じ順序で保持する。 -/
lemma monicKPrismUnaryConstantPointData_trace (n : ℕ) :
    familyChainCompositionInputTrace (monicKPrismUnaryConstantPointData F f n).witness =
      monicKPrismUnaryPointTrace F f n := by
  rw [monicKPrismUnaryConstantPointData, FamilyChainCompositeData.endpointTransport_trace,
    FamilyChainCompositeData.precomp_trace, familyChainCompositionInputTrace_eq]
  rfl

/-- 元の全木の同じ全三角形の前合成像を、同じ順序で厳密に保持する。 -/
lemma monicKPrismUnaryConstantPointData_triangles (n : ℕ) :
    familyChainCompositionTriangles (monicKPrismUnaryConstantPointData F f n).witness =
      (familyChainCompositionTriangles (monicKPrismUnaryCorrectionData F f n).witness).map
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (coherentArrowStringDirect f) ▷ (Δ[2] : SSet.{u})) ≫ ·) := by
  rw [monicKPrismUnaryConstantPointData, FamilyChainCompositeData.endpointTransport_triangles,
    FamilyChainCompositeData.precomp_triangles]

end SerrePositivity.KST.SConstruction
