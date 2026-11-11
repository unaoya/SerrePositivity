module

public import
  SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCoconeRightPrefixTriangleExtension
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.PointEdgeTransportCylinder
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ColimitAttachmentTransportCylinder

/-!
概要：元の右初面三角形の比較円柱を初辺へ制限し、付加辺と標準輸送の同じ円柱として保持する。
方針：初辺の二端の raw な式で表示を揃え、底と共通始点の固定条件を制限する。
規約：三角形の比較も付加辺も選び直さない。使われ方：中間評価と付加辺輸送の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
variable {A B C D : SSet.{u + 1}} {f : A ⟶ B} {g : A ⟶ C}
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) [Mono g] (p : D ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
  (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (f ≫ (i ≫ p))) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c)
  (dB : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (i ≫ p)) (dC : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (j ≫ p))
local notation "q" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (f ≫ (i ≫ p))
local notation "e₀" => SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitAttachmentApexEdge c hc g (j ≫ p)
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC)
local notation "v₀" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialFiberVertexAt q c (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex c) rfl
local notation "a₀" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitAttachmentRestrictionEdge c hc g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq
  hp p) dC
local notation "W" => SSet.yonedaEquiv.symm (SSet.Edge.edge a₀)
local notation "σ" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRightTriangle c hc f (i ≫ p) rfl dB
  g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC
local notation "T" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightPrefixTriangleComparison hp p c hc dB dC

/-- 同じ三角形比較円柱の初辺への制限。両端は元の付加辺と同じ標準点輸送。 -/
def specifiedCoconeRightPrefixFirstHomotopy :
    SSet.Homotopy W (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismVertexEvaluation (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.transportEdgePrism q e₀) v₀) := by
  let K := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp (T).homotopy (stdSimplex.δ (2 : Fin 3))
  refine
    { h := K.h
      h₀ := K.h₀.trans (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightPrefixRootedTriangle_first hp p c hc dB dC)
      h₁ := K.h₁.trans ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransportTriangleVertex_first q σ v₀).trans
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.standardTransportPointEdge_diagram q e₀ v₀))
      rel := by
        apply SSet.hom_ext
        intro n
        apply ConcreteCategory.hom_ext
        intro z
        exact False.elim z.1.property }

/-- 初辺の比較でも、元の三角形の同じ raw な円柱を保持する。 -/
lemma specifiedCoconeRightPrefixFirstHomotopy_raw :
    (specifiedCoconeRightPrefixFirstHomotopy hp p c hc dB dC).h =
      (stdSimplex.δ (2 : Fin 3) ▷ (Δ[1] : SSet.{u + 1})) ≫ (T).homotopy.h := rfl

/-- 制限した円柱の底は、元の付加頂点比較辺に定値な円柱である。 -/
lemma specifiedCoconeRightPrefixFirstHomotopy_projection :
    (specifiedCoconeRightPrefixFirstHomotopy hp p c hc dB dC).h ≫ q =
      fst (Δ[1] : SSet.{u + 1}) Δ[1] ≫ SSet.yonedaEquiv.symm (e₀).edge := by
  rw [specifiedCoconeRightPrefixFirstHomotopy_raw, Category.assoc, (T).projection,
    ← Category.assoc, whiskerRight_fst, Category.assoc,
    stdSimplex.δ_comp_yonedaEquiv_symm, (σ).d₂]

/-- 初辺の始点も、元の共通余錐の同じ点に全時刻で固定される。 -/
lemma specifiedCoconeRightPrefixFirstHomotopy_initial :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.scaffoldFirstVertex 1 ▷ (Δ[1] : SSet.{u + 1})) ≫
        (specifiedCoconeRightPrefixFirstHomotopy hp p c hc dB dC).h =
      fst (Δ[0] : SSet.{u + 1}) Δ[1] ≫ SSet.yonedaEquiv.symm (v₀).val := by
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.scaffoldFirstVertex 1 ≫ stdSimplex.δ (2 : Fin 3) =
      (stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (1 : Fin 3) :
        (Δ[0] : SSet.{u + 1}) ⟶ Δ[2]) := by
    rw [← _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.edgeInitial_firstVertex, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.triangleFirstInitial_firstVertex,
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.triangleLongInitial_firstVertex]
  have hs : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.scaffoldFirstVertex 1 ▷ (Δ[1] : SSet.{u + 1})) ≫
      (stdSimplex.δ (2 : Fin 3) ▷ (Δ[1] : SSet.{u + 1})) =
      ((stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (1 : Fin 3)) ▷ (Δ[1] : SSet.{u + 1})) :=
    (MonoidalCategory.comp_whiskerRight _ _ _).symm.trans
      (congrArg (fun z ↦ z ▷ (Δ[1] : SSet.{u + 1})) hi)
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.scaffoldFirstVertex 1 ▷ (Δ[1] : SSet.{u + 1})) ≫
    ((stdSimplex.δ (2 : Fin 3) ▷ (Δ[1] : SSet.{u + 1})) ≫ (T).homotopy.h) = _
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun z ↦ z ≫ (T).homotopy.h) hs).trans (T).initial)

/-- 元の三角形円柱から得る、付加辺自身の一点 prism 比較データ。 -/
abbrev specifiedCoconeRightPrefixFirstPointCylinder :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointEdgeTransportCylinder q e₀ v₀ W
    (specifiedCoconeRightPrefixFirstHomotopy hp p c hc dB dC)
    (specifiedCoconeRightPrefixFirstHomotopy_projection hp p c hc dB dC)
    (specifiedCoconeRightPrefixFirstHomotopy_initial hp p c hc dB dC)

local notation "w" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitAttachmentFiberVertex g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC
local notation "k" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitAttachmentCoconeEdge c hc g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC

/-- 初辺比較の終点を、一点からの同じ fiber 内のホモトピーとして保持する。 -/
abbrev specifiedCoconeRightPrefixFirstEndpointHomotopy :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointEdgeTransportEndpointHomotopy q e₀ v₀ W
    (specifiedCoconeRightPrefixFirstHomotopy hp p c hc dB dC)
    (specifiedCoconeRightPrefixFirstHomotopy_projection hp p c hc dB dC)
    (specifiedCoconeRightPrefixFirstHomotopy_initial hp p c hc dB dC)
    (SSet.yonedaEquiv.symm w) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.liftedEdgePointPrism_one q v₀ w k)

/-- 元の三角形円柱の初辺の終点の類は、既存の付加辺輸送同型の射である。 -/
lemma specifiedCoconeRightPrefixFirstEndpointHomotopy_hom :
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (specifiedCoconeRightPrefixFirstEndpointHomotopy hp p c hc dB dC)) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitAttachmentTransportPointIso c hc g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC).hom
        := by
  exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointEdgeTransportEndpointHomotopy_hom q e₀ v₀ W
    (specifiedCoconeRightPrefixFirstHomotopy hp p c hc dB dC)
    (specifiedCoconeRightPrefixFirstHomotopy_projection hp p c hc dB dC)
    (specifiedCoconeRightPrefixFirstHomotopy_initial hp p c hc dB dC)
    (SSet.yonedaEquiv.symm w) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.liftedEdgePointPrism_one q v₀ w k)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.liftedEdgePointPrism_zero q v₀ w k)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.liftedEdgePointPrism_projection q e₀ v₀ w k
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitAttachmentTransportCylinder_edge_projection c hc g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq
        hp p) dC))

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
