module
public import SerrePositivity.KST.Fibration.JointReflection
public import SerrePositivity.KST.SConstruction.GappedPushoutPreservation
public import SerrePositivity.KST.SConstruction.FullSubcomplexGappedReflection

/-! # 全 gapped S_n の両射影による零対象と押し出しの共同反映 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Fibration

/-- 元の共同反映条件を、全 gapped S_n の同じ二つの後合成射へ移す。 -/
lemma JointlyReflectsSData.sConstruction {P X A : StableModel.{u}}
    {p : P ⟶ X} {q : P ⟶ A} (h : JointlyReflectsSData p.val q.val) (n : ℕ) :
    JointlyReflectsSData ((sEndofunctor n).map p).val ((sEndofunctor n).map q).val where
  zero v hp hq := by
    have hp' := (gappedInclusion_preservesSConstructionData n X.carrier).1 _ hp
    have hq' := (gappedInclusion_preservesSConstructionData n A.carrier).1 _ hq
    change _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex ((sPostcompCofiber n p.val p.property ≫
      (gappedSubcomplex n X.carrier).ι).app _ v) at hp'
    change _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex ((sPostcompCofiber n q.val q.property ≫
      (gappedSubcomplex n A.carrier).ι).app _ v) at hq'
    rw [sPostcompCofiber_ι] at hp' hq'
    have hz := (h.ihom (arNerve n)).zero v.val hp' hq'
    exact ⟨isInitialVertex_fullSubcomplex_of_ambient _ v hz.1,
      isTerminalVertex_fullSubcomplex_of_ambient _ v hz.2⟩
  pushout F hp hq := by
    have hp' := (gappedInclusion_preservesSConstructionData n X.carrier).2 _ hp
    have hq' := (gappedInclusion_preservesSConstructionData n A.carrier).2 _ hq
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare ((F ≫ sPostcompCofiber n p.val p.property) ≫
      (gappedSubcomplex n X.carrier).ι) at hp'
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare ((F ≫ sPostcompCofiber n q.val q.property) ≫
      (gappedSubcomplex n A.carrier).ι) at hq'
    rw [Category.assoc, sPostcompCofiber_ι, ← Category.assoc] at hp' hq'
    apply isPushoutSquare_fullSubcomplex_of_ambient
      (fun v => IsGapped ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (arNerve n) P.carrier).symm v))
    exact (h.ihom (arNerve n)).pushout _ hp' hq'

end SerrePositivity.KST.Fibration
