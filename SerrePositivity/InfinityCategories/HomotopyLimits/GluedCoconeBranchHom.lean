module

public import SerrePositivity.InfinityCategories.HomotopyLimits.CoconeBranchHomComparison
public import SerrePositivity.InfinityCategories.HomotopyLimits.PartialColimitGluedBranchEdges

/-!
概要：貼った余錐の両枝の全 Hom の族を、span の実際の脚の前合成と同時に比較する。
方針：底の脚を厳密に被覆する枝の比較辺に、任意の余錐の全 Hom の制限比較を適用する。
規約：貼った余錐の余極限性は仮定しない。使われ方：共通 path end 上の普遍点の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section

/-- 余錐の制限への比較辺を、元の余錐頂点への実際の底の辺として表示する。 -/
def coconeRestrictionEdgeApex {K L X : SSet.{u}} {F : K ⟶ X}
    (i : L ⟶ K) (c : JoinCocone (i ≫ F)) (d : JoinCocone F)
    (k : (sliceUnder (i ≫ F)).Edge c (d.restrict i)) : X.Edge c.vertex d.vertex :=
  ⟨(k.map (sliceUnderProjection (i ≫ F))).edge,
    (k.map (sliceUnderProjection (i ≫ F))).src_eq,
    (k.map (sliceUnderProjection (i ≫ F))).tgt_eq.trans (d.vertex_restrict i)⟩

/-- 実際の枝の比較辺の射影による、元の余錐の全 Hom の制限の正方形。 -/
lemma coconePointHomFamily_rawBranch_homotopy {K L X : SSet.{u}} [Quasicategory X]
    {F : K ⟶ X} (i : L ⟶ K) (c : JoinCocone (i ≫ F)) (hc : IsColimitCone c)
    (d : JoinCocone F) (k : (sliceUnder (i ≫ F)).Edge c (d.restrict i)) (y : X _⦋0⦌) :
    Nonempty (SSet.Homotopy
      ((coconePointHomFamily d y ≫ cosliceRestrictionFiberMap F i y) ≫
        coconeMappingSpaceHomComparison c hc y)
      (coconeApexHomPrecomposition c d (coconeRestrictionEdgeApex i c d k) y)) := by
  have H := coconePointHomFamily_branch_homotopy c d (coconeRestrictionEdgeApex i c d k)
    y i rfl k rfl hc
  simpa only [normalizedCoconeRestrictionFiber_eq, eqToHom_refl, Category.comp_id] using H

/-- 貼った余錐には、span の実際の脚を保ち全 Hom の制限を計算する両枝の比較が存在。 -/
lemma exists_partialColimitPushout_cocone_with_branch_homotopies {A B C D : SSet.{u + 1}}
    {f : A ⟶ B} {g : A ⟶ C} {i : B ⟶ D} {j : C ⟶ D}
    (hp : IsPushout f g i j) [Mono g] (p : D ⟶ SpaceInfinity.{u})
    (c : JoinCocone (f ≫ (i ≫ p))) (hc : IsColimitCone c)
    (dB : JoinCocone (i ≫ p)) (hB : IsColimitCone dB)
    (dC : JoinCocone (j ≫ p)) (hC : IsColimitCone dC) :
    ∃ (d : JoinCocone p) (eB : SpaceInfinity.Edge dB.vertex d.vertex)
      (eC : SpaceInfinity.Edge dC.vertex d.vertex),
      d.vertex = spaceInfinityVertex
          (partialColimitPushoutObject c hc f (i ≫ p) rfl dB
            g (j ≫ p) (coconePushoutBoundary_eq hp p) dC) ∧
        eB.edge = (partialColimitSpanLeftLeg c hc f (i ≫ p) rfl dB
          g (j ≫ p) (coconePushoutBoundary_eq hp p) dC).edge ∧
        eC.edge = (partialColimitSpanRightLeg c hc f (i ≫ p) rfl dB
          g (j ≫ p) (coconePushoutBoundary_eq hp p) dC).edge ∧
        ∀ y : SpaceInfinity.{u} _⦋0⦌,
          Nonempty (SSet.Homotopy
            ((coconePointHomFamily d y ≫ cosliceRestrictionFiberMap p i y) ≫
              coconeMappingSpaceHomComparison dB hB y)
            (coconeApexHomPrecomposition dB d eB y)) ∧
          Nonempty (SSet.Homotopy
            ((coconePointHomFamily d y ≫ cosliceRestrictionFiberMap p j y) ≫
              coconeMappingSpaceHomComparison dC hC y)
            (coconeApexHomPrecomposition dC d eC y)) := by
  obtain ⟨d, kB, kC, hv, heB, heC⟩ :=
    exists_partialColimitPushout_cocone_with_branch_edges hp p c hc dB dC
  refine ⟨d, coconeRestrictionEdgeApex i dB d kB,
    coconeRestrictionEdgeApex j dC d kC, hv, heB, heC, ?_⟩
  intro y
  exact ⟨coconePointHomFamily_rawBranch_homotopy i dB hB d kB y,
    coconePointHomFamily_rawBranch_homotopy j dC hC d kC y⟩

end
end SerrePositivity.InfinityCategories.HomotopyLimits
