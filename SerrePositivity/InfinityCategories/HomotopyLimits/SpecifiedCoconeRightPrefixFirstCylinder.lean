module

public import
  SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeRightPrefixTriangleExtension
public import SerrePositivity.InfinityCategories.HomotopyLimits.PointEdgeTransportCylinder
public import SerrePositivity.InfinityCategories.HomotopyLimits.ColimitAttachmentTransportCylinder

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
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {A B C D : SSet.{u + 1}} {f : A ⟶ B} {g : A ⟶ C}
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) [Mono g] (p : D ⟶ SpaceInfinity.{u})
  (c : JoinCocone (f ≫ (i ≫ p))) (hc : IsColimitCone c)
  (dB : JoinCocone (i ≫ p)) (dC : JoinCocone (j ≫ p))
local notation "q" => sliceUnderProjection (f ≫ (i ≫ p))
local notation "e₀" => SSet.Edge.ofTruncated (colimitAttachmentApexEdge c hc g (j ≫ p)
  (coconePushoutBoundary_eq hp p) dC)
local notation "v₀" => initialFiberVertexAt q c (JoinCocone.vertex c) rfl
local notation "a₀" => colimitAttachmentRestrictionEdge c hc g (j ≫ p) (coconePushoutBoundary_eq
  hp p) dC
local notation "W" => SSet.yonedaEquiv.symm (SSet.Edge.edge a₀)
local notation "σ" => partialColimitSpanRightTriangle c hc f (i ≫ p) rfl dB
  g (j ≫ p) (coconePushoutBoundary_eq hp p) dC
local notation "T" => specifiedCoconeRightPrefixTriangleComparison hp p c hc dB dC

/-- 同じ三角形比較円柱の初辺への制限。両端は元の付加辺と同じ標準点輸送。 -/
def specifiedCoconeRightPrefixFirstHomotopy :
    SSet.Homotopy W (prismVertexEvaluation (transportEdgePrism q e₀) v₀) := by
  let K := functorHomotopyPrecomp (T).homotopy (stdSimplex.δ (2 : Fin 3))
  refine
    { h := K.h
      h₀ := K.h₀.trans (specifiedCoconeRightPrefixRootedTriangle_first hp p c hc dB dC)
      h₁ := K.h₁.trans ((coherentTransportTriangleVertex_first q σ v₀).trans
        (standardTransportPointEdge_diagram q e₀ v₀))
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
    (scaffoldFirstVertex 1 ▷ (Δ[1] : SSet.{u + 1})) ≫
        (specifiedCoconeRightPrefixFirstHomotopy hp p c hc dB dC).h =
      fst (Δ[0] : SSet.{u + 1}) Δ[1] ≫ SSet.yonedaEquiv.symm (v₀).val := by
  have hi : scaffoldFirstVertex 1 ≫ stdSimplex.δ (2 : Fin 3) =
      (stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (1 : Fin 3) :
        (Δ[0] : SSet.{u + 1}) ⟶ Δ[2]) := by
    rw [← edgeInitial_firstVertex, triangleFirstInitial_firstVertex,
      triangleLongInitial_firstVertex]
  have hs : (scaffoldFirstVertex 1 ▷ (Δ[1] : SSet.{u + 1})) ≫
      (stdSimplex.δ (2 : Fin 3) ▷ (Δ[1] : SSet.{u + 1})) =
      ((stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (1 : Fin 3)) ▷ (Δ[1] : SSet.{u + 1})) :=
    (MonoidalCategory.comp_whiskerRight _ _ _).symm.trans
      (congrArg (fun z ↦ z ▷ (Δ[1] : SSet.{u + 1})) hi)
  change (scaffoldFirstVertex 1 ▷ (Δ[1] : SSet.{u + 1})) ≫
    ((stdSimplex.δ (2 : Fin 3) ▷ (Δ[1] : SSet.{u + 1})) ≫ (T).homotopy.h) = _
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun z ↦ z ≫ (T).homotopy.h) hs).trans (T).initial)

/-- 元の三角形円柱から得る、付加辺自身の一点 prism 比較データ。 -/
abbrev specifiedCoconeRightPrefixFirstPointCylinder :=
  pointEdgeTransportCylinder q e₀ v₀ W
    (specifiedCoconeRightPrefixFirstHomotopy hp p c hc dB dC)
    (specifiedCoconeRightPrefixFirstHomotopy_projection hp p c hc dB dC)
    (specifiedCoconeRightPrefixFirstHomotopy_initial hp p c hc dB dC)

local notation "w" => colimitAttachmentFiberVertex g (j ≫ p) (coconePushoutBoundary_eq hp p) dC
local notation "k" => colimitAttachmentCoconeEdge c hc g (j ≫ p) (coconePushoutBoundary_eq hp p) dC

/-- 初辺比較の終点を、一点からの同じ fiber 内のホモトピーとして保持する。 -/
abbrev specifiedCoconeRightPrefixFirstEndpointHomotopy :=
  pointEdgeTransportEndpointHomotopy q e₀ v₀ W
    (specifiedCoconeRightPrefixFirstHomotopy hp p c hc dB dC)
    (specifiedCoconeRightPrefixFirstHomotopy_projection hp p c hc dB dC)
    (specifiedCoconeRightPrefixFirstHomotopy_initial hp p c hc dB dC)
    (SSet.yonedaEquiv.symm w) (liftedEdgePointPrism_one q v₀ w k)

/-- 元の三角形円柱の初辺の終点の類は、既存の付加辺輸送同型の射である。 -/
lemma specifiedCoconeRightPrefixFirstEndpointHomotopy_hom :
    SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
      (specifiedCoconeRightPrefixFirstEndpointHomotopy hp p c hc dB dC)) =
      (colimitAttachmentTransportPointIso c hc g (j ≫ p) (coconePushoutBoundary_eq hp p) dC).hom
        := by
  exact pointEdgeTransportEndpointHomotopy_hom q e₀ v₀ W
    (specifiedCoconeRightPrefixFirstHomotopy hp p c hc dB dC)
    (specifiedCoconeRightPrefixFirstHomotopy_projection hp p c hc dB dC)
    (specifiedCoconeRightPrefixFirstHomotopy_initial hp p c hc dB dC)
    (SSet.yonedaEquiv.symm w) (liftedEdgePointPrism_one q v₀ w k)
    (liftedEdgePointPrism_zero q v₀ w k)
    (liftedEdgePointPrism_projection q e₀ v₀ w k
      (colimitAttachmentTransportCylinder_edge_projection c hc g (j ≫ p) (coconePushoutBoundary_eq
        hp p) dC))

end
end SerrePositivity.InfinityCategories.HomotopyLimits
