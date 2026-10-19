module

public import SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeRestrictionEdges
public import SerrePositivity.InfinityCategories.HomotopyLimits.TransportFibreEdgeComposition
public import SerrePositivity.InfinityCategories.HomotopyLimits.GluedCoconeBranchHom

/-!
概要：指定経路で構成した特定の余錐に、元の span の両脚を被覆する比較辺を付ける。
方針：右修正経路自身の辺を輸送辺へ合成し、元の修正辺を面として持つ三角形も保持する。
規約：存在だけの別の貼り合わせ余錐へ置き換えない。使われ方：特定の余錐の全 Hom の族の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {A B C D : SSet.{u + 1}} {f : A ⟶ B} {g : A ⟶ C}
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) [Mono g] (p : D ⟶ SpaceInfinity.{u})
  (c : JoinCocone (f ≫ (i ≫ p))) (hc : IsColimitCone c)
  (dB : JoinCocone (i ≫ p)) (dC : JoinCocone (j ≫ p))

/-- 指定した特定の余錐の両枝へ、実際の脚を保つ比較辺と右修正辺そのものの合成三角形が存在。 -/
lemma exists_specifiedPathCocone_branch_comparisons :
    ∃ (kB : (sliceUnder (i ≫ p)).Edge dB
        ((partialColimitSpecifiedPathCocone hp p c hc dB dC).restrict i))
      (kC : (sliceUnder (j ≫ p)).Edge dC
        ((partialColimitSpecifiedPathCocone hp p c hc dB dC).restrict j)),
      (kB.map (sliceUnderProjection (i ≫ p))).edge =
          (partialColimitSpanLeftLeg c hc f (i ≫ p) rfl dB
            g (j ≫ p) (coconePushoutBoundary_eq hp p) dC).edge ∧
        (kC.map (sliceUnderProjection (j ≫ p))).edge =
          (partialColimitSpanRightLeg c hc f (i ≫ p) rfl dB
            g (j ≫ p) (coconePushoutBoundary_eq hp p) dC).edge ∧
        ∃ (k₀ : (sliceUnder (j ≫ p)).Edge dC
            (transportedCoconeVertex dC (partialColimitSpanRightLeg c hc f (i ≫ p) rfl dB
              g (j ≫ p) (coconePushoutBoundary_eq hp p) dC)).val)
          (s : (sliceUnder (j ≫ p)) _⦋2⦌),
          (sliceUnder (j ≫ p)).δ 2 s = k₀.edge ∧
          (sliceUnder (j ≫ p)).δ 0 s =
            (partialColimitSpecifiedCorrectionCosliceEdge hp p c hc dB dC).edge ∧
          (sliceUnder (j ≫ p)).δ 1 s = kC.edge ∧
          (sliceUnderProjection (j ≫ p)).app (Opposite.op ⦋2⦌) s =
            (SSet.Edge.CompStruct.compId
              (partialColimitSpanRightLeg c hc f (i ≫ p) rfl dB
                g (j ≫ p) (coconePushoutBoundary_eq hp p) dC)).simplex := by
  let eB := partialColimitSpanLeftLeg c hc f (i ≫ p) rfl dB
    g (j ≫ p) (coconePushoutBoundary_eq hp p) dC
  let eC := partialColimitSpanRightLeg c hc f (i ≫ p) rfl dB
    g (j ≫ p) (coconePushoutBoundary_eq hp p) dC
  obtain ⟨kB, hkB⟩ := exists_edge_of_transport_point (sliceUnderProjection (i ≫ p)) eB
    (edgeTransport (sliceUnderProjection (i ≫ p)) eB)
    (edgeTransport_isTransport (sliceUnderProjection (i ≫ p)) eB)
    (initialFiberVertexAt (sliceUnderProjection (i ≫ p)) dB dB.vertex rfl)
  let lB : (sliceUnder (i ≫ p)).Edge dB
      ((partialColimitSpecifiedPathCocone hp p c hc dB dC).restrict i) :=
    ⟨kB.edge, kB.src_eq, kB.tgt_eq.trans
      ((congrArg Subtype.val (partialColimitSpecifiedFiberVertex_left hp p c hc dB dC)).symm.trans
        (coconeRestrictionFiber_vertex_val i _
          (partialColimitSpecifiedFiberVertex hp p c hc dB dC)))⟩
  obtain ⟨k₀, kC, s, _, hkC, h₂, h₀, h₁, ht⟩ :=
      exists_transport_composition_faces_of_fibre_edge
    (sliceUnderProjection (j ≫ p)) eC
    (edgeTransport (sliceUnderProjection (j ≫ p)) eC)
    (edgeTransport_isTransport (sliceUnderProjection (j ≫ p)) eC)
    (initialFiberVertexAt (sliceUnderProjection (j ≫ p)) dC dC.vertex rfl)
    ((cosliceRestrictionFiberMap p j _).app (Opposite.op ⦋0⦌)
      (partialColimitSpecifiedFiberVertex hp p c hc dB dC))
    (partialColimitSpecifiedCorrectionEdge hp p c hc dB dC)
  let lC : (sliceUnder (j ≫ p)).Edge dC
      ((partialColimitSpecifiedPathCocone hp p c hc dB dC).restrict j) :=
    ⟨kC.edge, kC.src_eq, kC.tgt_eq.trans (coconeRestrictionFiber_vertex_val j _
      (partialColimitSpecifiedFiberVertex hp p c hc dB dC))⟩
  let l₀ : (sliceUnder (j ≫ p)).Edge dC (transportedCoconeVertex dC eC).val :=
    ⟨k₀.edge, k₀.src_eq, k₀.tgt_eq⟩
  refine ⟨lB, lC, ?_, ?_, l₀, s, ?_, ?_, ?_, ht⟩
  · change (sliceUnderProjection (i ≫ p)).app (Opposite.op ⦋1⦌) kB.edge = eB.edge
    exact hkB
  · change (sliceUnderProjection (j ≫ p)).app (Opposite.op ⦋1⦌) kC.edge = eC.edge
    exact hkC
  · simpa only [l₀, SSet.Edge.edge, SSet.Edge.toTruncated] using h₂
  · simpa only [partialColimitSpecifiedCorrectionCosliceEdge, SSet.Edge.edge,
      SSet.Edge.toTruncated] using h₀
  · simpa only [lC, SSet.Edge.edge, SSet.Edge.toTruncated] using h₁

/-- 指定経路で作った特定の余錐の全 Hom の族を、両脚の前合成と比較する。 -/
lemma exists_specifiedPathCocone_branch_homotopies
    (hB : IsColimitCone dB) (hC : IsColimitCone dC) :
    ∃ (eB : SpaceInfinity.Edge dB.vertex
        (partialColimitSpecifiedPathCocone hp p c hc dB dC).vertex)
      (eC : SpaceInfinity.Edge dC.vertex
        (partialColimitSpecifiedPathCocone hp p c hc dB dC).vertex),
      eB.edge = (partialColimitSpanLeftLeg c hc f (i ≫ p) rfl dB
        g (j ≫ p) (coconePushoutBoundary_eq hp p) dC).edge ∧
      eC.edge = (partialColimitSpanRightLeg c hc f (i ≫ p) rfl dB
        g (j ≫ p) (coconePushoutBoundary_eq hp p) dC).edge ∧
      ∀ y : SpaceInfinity.{u} _⦋0⦌,
        Nonempty (SSet.Homotopy
          ((coconePointHomFamily (partialColimitSpecifiedPathCocone hp p c hc dB dC) y ≫
            cosliceRestrictionFiberMap p i y) ≫ coconeMappingSpaceHomComparison dB hB y)
          (coconeApexHomPrecomposition dB
            (partialColimitSpecifiedPathCocone hp p c hc dB dC) eB y)) ∧
        Nonempty (SSet.Homotopy
          ((coconePointHomFamily (partialColimitSpecifiedPathCocone hp p c hc dB dC) y ≫
            cosliceRestrictionFiberMap p j y) ≫ coconeMappingSpaceHomComparison dC hC y)
          (coconeApexHomPrecomposition dC
            (partialColimitSpecifiedPathCocone hp p c hc dB dC) eC y)) := by
  obtain ⟨kB, kC, heB, heC, _⟩ :=
    exists_specifiedPathCocone_branch_comparisons hp p c hc dB dC
  refine ⟨coconeRestrictionEdgeApex i dB _ kB,
    coconeRestrictionEdgeApex j dC _ kC, heB, heC, ?_⟩
  intro y
  exact ⟨coconePointHomFamily_rawBranch_homotopy i dB hB _ kB y,
    coconePointHomFamily_rawBranch_homotopy j dC hC _ kC y⟩

end
end SerrePositivity.InfinityCategories.HomotopyLimits
