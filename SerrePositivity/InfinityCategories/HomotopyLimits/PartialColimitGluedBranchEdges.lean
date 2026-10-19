module

public import SerrePositivity.InfinityCategories.HomotopyLimits.TransportedCoconeEdges
public import SerrePositivity.InfinityCategories.HomotopyLimits.PartialColimitSpanCocone

/-!
概要：部分余極限 span の普遍余錐の実際の脚を保つ、元の図式の余錐と枝への比較辺を構成する。
方針：二枝の合成三角形から貼り合わせ、修正された右枝へも元の脚を被覆する辺を持ち上げる。
規約：元の図式の余極限性は結論に含めない。使われ方：貼った余錐の全 Hom の普遍点の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section

/-- 元の coherent 図式に、部分余極限 span の実際の両脚を保つ比較辺付きの余錐が存在。 -/
lemma exists_partialColimitPushout_cocone_with_branch_edges {A B C D : SSet.{u + 1}}
    {f : A ⟶ B} {g : A ⟶ C} {i : B ⟶ D} {j : C ⟶ D}
    (hp : IsPushout f g i j) [Mono g] (p : D ⟶ SpaceInfinity.{u})
    (c : JoinCocone (f ≫ (i ≫ p))) (hc : IsColimitCone c)
    (dB : JoinCocone (i ≫ p)) (dC : JoinCocone (j ≫ p)) :
    ∃ (d : JoinCocone p)
      (kB : (sliceUnder (i ≫ p)).Edge dB (d.restrict i))
      (kC : (sliceUnder (j ≫ p)).Edge dC (d.restrict j)),
      d.vertex = spaceInfinityVertex
          (partialColimitPushoutObject c hc f (i ≫ p) rfl dB
            g (j ≫ p) (coconePushoutBoundary_eq hp p) dC) ∧
        ((kB.map (sliceUnderProjection (i ≫ p))).edge) =
          (partialColimitSpanLeftLeg c hc f (i ≫ p) rfl dB
            g (j ≫ p) (coconePushoutBoundary_eq hp p) dC).edge ∧
        ((kC.map (sliceUnderProjection (j ≫ p))).edge) =
          (partialColimitSpanRightLeg c hc f (i ≫ p) rfl dB
            g (j ≫ p) (coconePushoutBoundary_eq hp p) dC).edge := by
  obtain ⟨d, kB, kC, hv, hB, hC⟩ := exists_cocone_glue_with_branch_edges hp p c hc dB dC
    (partialColimitSpanLeftLeg c hc f (i ≫ p) rfl dB
      g (j ≫ p) (coconePushoutBoundary_eq hp p) dC)
    (partialColimitSpanRightLeg c hc f (i ≫ p) rfl dB
      g (j ≫ p) (coconePushoutBoundary_eq hp p) dC)
    (partialColimitSpanLegs_composites c hc f (i ≫ p) rfl dB
      g (j ≫ p) (coconePushoutBoundary_eq hp p) dC)
  refine ⟨d, kB, kC, hv.trans ?_, hB, hC⟩
  exact (coherentCoconeOfDiagramEq_vertex _ _).trans
    (partialColimitPushoutCocone_vertex c hc f (i ≫ p) rfl dB
      g (j ≫ p) (coconePushoutBoundary_eq hp p) dC)

end
end SerrePositivity.InfinityCategories.HomotopyLimits
