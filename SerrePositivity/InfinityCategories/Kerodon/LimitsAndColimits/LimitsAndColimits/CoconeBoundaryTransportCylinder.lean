module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.MapTransportCylinder
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ColimitAttachmentTransportIso

/-!
概要：指定境界経路に含まれる制限の輸送自然性を、同じ相対円柱から実現する。
方針：全始点の自然性円柱を元の余錐の点で評価し、既存の同型の類を保持する。
規約：元の辺・余錐・制限を変更しない。使われ方：共通長辺の延長空間内での指定路の比較。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
noncomputable section
variable {A C X : SSet.{u}} [Quasicategory X] {p : A ⟶ X}
  (i : A ⟶ C) (F : C ⟶ X) (hi : i ≫ F = p) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone F)
  {y : X _⦋0⦌} (e : X.Edge d.vertex y)
local notation "qF" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection F
local notation "qA" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p
local notation "r" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestriction F i hi
local notation "hr" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestriction_projection F i hi
local notation "v" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialFiberVertexAt qF d (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex d) rfl
local notation "V" => SSet.yonedaEquiv.symm v

/-- 輸送後に制限する族の始点表示を、元の輸送余錐の境界へ厳密に揃える。 -/
lemma coconeBoundaryTransport_source :
    V ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport qF e ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber F i hi y) =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.transportedCoconeVertex d e) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber F i hi y :=
  (Category.assoc _ _ _).symm.trans (congrArg
    (fun z ↦ z ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber F i hi y)
    (SSet.yonedaEquiv_symm_comp v (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport qF e)))

/-- 制限後に輸送する族も、元の付加境界の点図式に厳密に揃える。 -/
lemma coconeBoundaryTransport_target :
    V ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber F i hi d.vertex ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport qA e) =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitAttachmentFiberVertex i F hi d) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport qA e := by
  have hb : V ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber F i hi d.vertex =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitAttachmentFiberVertex i F hi d) := by
    rw [SSet.yonedaEquiv_symm_comp]
    exact congrArg SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber_vertex F i hi d)
  exact (Category.assoc _ _ _).symm.trans (congrArg (fun z ↦ z ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport qA e) hb)

/-- 指定境界路の自然性部分を実現する、同じ底・初期値固定の全始点の円柱。 -/
def coconeBoundaryTransportCylinderData := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.mapTransportCylinderData qF qA r hr e

/-- 元の余錐の点で評価した、輸送と制限の実際の比較円柱。 -/
def coconeBoundaryTransportHomotopy : SSet.Homotopy
    (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.transportedCoconeVertex d e) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber F i hi y)
    (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitAttachmentFiberVertex i F hi d) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport qA e) := by
  let H := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.mapTransportEndpointHomotopy qF qA r hr e) V
  exact
    { h := H.h
      h₀ := H.h₀.trans (coconeBoundaryTransport_source i F hi d e)
      h₁ := H.h₁.trans (coconeBoundaryTransport_target i F hi d e)
      rel := by
        apply SSet.hom_ext
        intro n
        apply ConcreteCategory.hom_ext
        intro z
        exact False.elim z.1.property }

set_option maxHeartbeats 800000 in
-- 既存の同型の両端表示と、正規化した fiber 制限の頂点を同時に照合する。
/-- 端点表示を揃えた既存の同型も、元の全始点の自然性同型の同じ点評価を保つ。 -/
lemma coconeBoundaryTransportPointIso_hom_arrow :
    Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeBoundaryTransportPointIso i F hi d e).hom =
      Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationMap_transportIso qF qA r hr e) V).hom :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorIsoTransport_hom_arrow
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationMap_transportIso qF qA r hr e) V)
    (coconeBoundaryTransport_source i F hi d e)
    (coconeBoundaryTransport_target i F hi d e)

/-- 円柱の辺の類は、元の指定境界経路で使う制限の輸送自然性同型の射そのもの。 -/
lemma coconeBoundaryTransportHomotopy_hom :
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (coconeBoundaryTransportHomotopy i F hi d e)) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeBoundaryTransportPointIso i F hi d e).hom := by
  apply Arrow.mk_injective _ _
  refine (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomotopy_hom_arrow_of_h_eq
    (coconeBoundaryTransportHomotopy i F hi d e)
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.mapTransportEndpointHomotopy qF qA r hr e) V) rfl).trans ?_
  have h : SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.mapTransportEndpointHomotopy qF qA r hr e) V)) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationMap_transportIso qF qA r hr e) V).hom := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp_hom, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.mapTransportEndpointHomotopy_hom]
    rfl
  exact (congrArg Arrow.mk h).trans (coconeBoundaryTransportPointIso_hom_arrow i F hi d e).symm

/-- 終点円柱の raw な射は、同じ全始点の自然性円柱を元の点で制限したもの。 -/
lemma coconeBoundaryTransportHomotopy_projection :
    (coconeBoundaryTransportHomotopy i F hi d e).h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι qA y =
      (V ▷ (Δ[1] : SSet.{u})) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber qF d.vertex) ▷ (Δ[1] : SSet.{u})) ≫
          (coconeBoundaryTransportCylinderData i F hi d e).homotopy.h :=
  (Category.assoc _ _ _).trans (congrArg (fun z ↦ (V ▷ (Δ[1] : SSet.{u})) ≫ z)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.mapTransportEndpointHomotopy_projection qF qA r hr e))

end
end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
