module

public import SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SectionsConeComposition
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.LimitVertexIsoComposition

/-!
概要：集合重みの同じ制限錐の普遍辺と、指定極限の比較の合成則。
方針：錐のホモトピー圏の終対象への射の一意性を使い、同じ頂点射影で写す。
規約：HTT §1.2.13、Kerodon §7.1（Tag 02H1）の既存構成の法則。
使われ方：S8 の指定値の比較を、切断の元の普遍辺に照合する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
namespace SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetWeight
variable {I : Type u} [SmallCategory I] {P Q : I ⥤ Type u}
variable {E : SSet.{u + 1}} [Quasicategory E]

/-- 指定した標的極限を比較してからでも、同じ制限錐の普遍辺になる。 -/
lemma sectionsConeMap_limitConeIso_hom (φ : P ⟶ Q)
    (O : (SSet.uliftFunctor.{u + 1, u}).obj (nerve I) ⟶ E)
    (c d : JoinCone (diagram P O)) (hc : IsLimitCone c) (hd : IsLimitCone d)
    (q : JoinCone (diagram Q O)) :
    Truncated.HomotopyCategory.homMk (sectionsConeMap φ O c hc q).toTruncated ≫
      (limitConeIso c d hc hd).hom =
        Truncated.HomotopyCategory.homMk (sectionsConeMap φ O d hd q).toTruncated :=
  hd.isTerminalHo.hom_ext _ _

/-- 同じ錐の普遍辺の合成則を、頂点の射へ射影した等式。 -/
lemma sectionsConeMap_limitVertexIso_hom (φ : P ⟶ Q)
    (O : (SSet.uliftFunctor.{u + 1, u}).obj (nerve I) ⟶ E)
    (c d : JoinCone (diagram P O)) (hc : IsLimitCone c) (hd : IsLimitCone d)
    (q : JoinCone (diagram Q O)) :
    (hoFunctor.map (sliceOverProjection (diagram P O))).toFunctor.map
        (Truncated.HomotopyCategory.homMk (sectionsConeMap φ O c hc q).toTruncated) ≫
      (limitVertexIso c d hc hd).hom =
    (hoFunctor.map (sliceOverProjection (diagram P O))).toFunctor.map
        (Truncated.HomotopyCategory.homMk (sectionsConeMap φ O d hd q).toTruncated) := by
  change (hoFunctor.map (sliceOverProjection (diagram P O))).toFunctor.map
      (Truncated.HomotopyCategory.homMk (sectionsConeMap φ O c hc q).toTruncated) ≫
    (hoFunctor.map (sliceOverProjection (diagram P O))).toFunctor.map
      (limitConeIso c d hc hd).hom = _
  rw [← CategoryTheory.Functor.map_comp, sectionsConeMap_limitConeIso_hom]

end SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetWeight
