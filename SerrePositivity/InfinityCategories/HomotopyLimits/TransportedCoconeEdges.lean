module

public import SerrePositivity.InfinityCategories.HomotopyLimits.TransportComponentEdgeLift
public import SerrePositivity.InfinityCategories.HomotopyLimits.TransportedCoconeGluing

/-!
概要：貼り合わせた二枝に、span の実際の脚を被覆する余錐圏の辺を付ける。
方針：輸送像と同じ fiber 成分の点への厳密な辺の持ち上げを、右枝の修正後に適用する。
規約：枝の余極限性は不要。使われ方：貼った余錐の全 Hom の族を実際の span の脚と比較する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section

/-- 輸送された余錐と同じ固定終点成分の余錐へ、指定した頂点の辺を厳密に被覆する比較辺が存在。 -/
lemma exists_cocone_edge_of_transport_component {K X : SSet.{u}} [Quasicategory X]
    {F : K ⟶ X} (d : JoinCocone F) {y : X _⦋0⦌} (e : X.Edge d.vertex y)
    (z : (coconeMappingSpace F y) _⦋0⦌)
    (hz : SSet.π₀.mk z = SSet.π₀.mk (transportedCoconeVertex d e)) :
    ∃ k : (sliceUnder F).Edge d z.val,
      ((k.map (sliceUnderProjection F)).edge) = e.edge :=
  exists_edge_over_of_edgeTransport_component (sliceUnderProjection F) e
    (initialFiberVertexAt (sliceUnderProjection F) d d.vertex rfl) z hz.symm

/-- 元の図式を貼った余錐の両枝へ、指定した span の脚そのものを被覆する実際の比較辺が存在。 -/
lemma exists_cocone_glue_with_branch_edges {A B C D X : SSet.{u}} [Quasicategory X]
    {f : A ⟶ B} {g : A ⟶ C} {i : B ⟶ D} {j : C ⟶ D}
    (hp : IsPushout f g i j) [Mono g] (p : D ⟶ X)
    (c : JoinCocone (f ≫ (i ≫ p))) (hc : IsColimitCone c)
    (dB : JoinCocone (i ≫ p)) (dC : JoinCocone (j ≫ p))
    {y : X _⦋0⦌} (eB : X.Edge dB.vertex y) (eC : X.Edge dC.vertex y)
    (h : SSet.Truncated.HomotopyCategory.homMk (colimitAttachmentApexEdge c hc f (i ≫ p) rfl dB) ≫
        SSet.Truncated.HomotopyCategory.homMk eB.toTruncated =
      SSet.Truncated.HomotopyCategory.homMk
          (colimitAttachmentApexEdge c hc g (j ≫ p) (coconePushoutBoundary_eq hp p) dC) ≫
        SSet.Truncated.HomotopyCategory.homMk eC.toTruncated) :
    ∃ (d : JoinCocone p)
      (kB : (sliceUnder (i ≫ p)).Edge dB (d.restrict i))
      (kC : (sliceUnder (j ≫ p)).Edge dC (d.restrict j)),
      d.vertex = y ∧ ((kB.map (sliceUnderProjection (i ≫ p))).edge) = eB.edge ∧
        ((kC.map (sliceUnderProjection (j ≫ p))).edge) = eC.edge := by
  obtain ⟨d, z, hB, hC, hv, hz⟩ :=
    exists_cocone_glue_of_apex_composites hp p c hc dB dC eB eC h
  obtain ⟨kB, hkB⟩ := exists_cocone_edge_of_transport_component dB eB
    (transportedCoconeVertex dB eB) rfl
  obtain ⟨kC, hkC⟩ := exists_cocone_edge_of_transport_component dC eC z hz
  let lB : (sliceUnder (i ≫ p)).Edge dB (d.restrict i) :=
    ⟨kB.edge, kB.src_eq, kB.tgt_eq.trans hB.symm⟩
  let lC : (sliceUnder (j ≫ p)).Edge dC (d.restrict j) :=
    ⟨kC.edge, kC.src_eq, kC.tgt_eq.trans hC.symm⟩
  exact ⟨d, lB, lC, hv, hkB, hkC⟩

end
end SerrePositivity.InfinityCategories.HomotopyLimits
