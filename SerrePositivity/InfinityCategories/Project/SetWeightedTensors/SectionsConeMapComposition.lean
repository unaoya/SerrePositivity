module

public import SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetSectionsRestriction

/-!
概要：集合重みの合成に沿う元の指定普遍辺のホモトピー類の合成則。
方針：既存の制限の全関手で普遍辺を写し、同じ錐の終対象への一意性を使う。
規約：HTT §1.2.13、Kerodon §7.1（Tag 02H1）の既存構成の合成則。
使われ方：S8 の局所同値の像への分解を、元の指定切断射へ戻す。
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

/-- 同じ制限の全関手で二段の普遍辺を写して合成すると、元の合成重みの普遍辺になる。 -/
lemma sectionsConeMap_comp_hom {I : Type u} [SmallCategory I]
    {P Q R : I ⥤ Type u} {E : SSet.{u + 1}} [Quasicategory E]
    (φ : P ⟶ Q) (ψ : Q ⟶ R)
    (O : (SSet.uliftFunctor.{u + 1, u}).obj (nerve I) ⟶ E)
    (cP : JoinCone (diagram P O)) (hcP : IsLimitCone cP)
    (cQ : JoinCone (diagram Q O)) (hcQ : IsLimitCone cQ)
    (cR : JoinCone (diagram R O)) :
    let h0 := (restrictSectionsFunctor_vertex φ O (restrictSectionsCone ψ O cR)).trans
      (restrictSectionsCone_comp φ O ψ cR)
    let h1 := restrictSectionsFunctor_vertex φ O cQ
    eqToHom (congrArg HomotopyCategory.mk h0.symm) ≫
      (hoFunctor.map (restrictSectionsFunctor φ O)).toFunctor.map
        (Truncated.HomotopyCategory.homMk (sectionsConeMap ψ O cQ hcQ cR).toTruncated) ≫
      eqToHom (congrArg HomotopyCategory.mk h1) ≫
        Truncated.HomotopyCategory.homMk (sectionsConeMap φ O cP hcP cQ).toTruncated =
    Truncated.HomotopyCategory.homMk (sectionsConeMap (φ ≫ ψ) O cP hcP cR).toTruncated := by
  exact hcP.isTerminalHo.hom_ext _ _

end SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetWeight
