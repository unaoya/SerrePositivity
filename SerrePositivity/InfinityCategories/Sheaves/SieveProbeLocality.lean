module

public import SerrePositivity.InfinityCategories.Sheaves.SieveSectionsCriterion
public import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.SieveTensorSectionsNaturality
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.LocalObjects

/-!
概要：同じ篩テンソル辺の局所性を、切断比較辺の写像空間で判定する。
方針：G8の元の全四角形と両縦辺の同値性を用いて同値性を移す。
使われ方：HTT 5.5.4.15・6.2.2.7、Kerodon Tag 06VH の層生成辺の局所性。
規約：独立な写像空間比較を選ばず、指定された切断錐とG8の比較を使う。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Project.SetWeightedTensors
open SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C] {E : SSet.{u+1}} [Quasicategory E]

/-- 元の篩テンソル辺への局所性は、同じ切断辺の後合成の同値性と同値。 -/
lemma sieveTensorEdge_locality_iff {U : C} (S : Sieve U) (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E)
    (M : E _⦋0⦌) (F : Presheaf C E)
    (cS : JoinCone (SetWeight.diagram S.functor F)) (hcS : IsLimitCone cS)
    (cU : JoinCone (SetWeight.diagram (yoneda.obj U) F)) (hcU : IsLimitCone cU) :
    IsQCatEquivalence (precompose (functorVertex F)
      (Truncated.HomotopyCategory.homMk (SetWeight.sieveTensorEdge S hE M).toTruncated)) ↔
    IsQCatEquivalence (postcompose M
      (Truncated.HomotopyCategory.homMk
        (SetWeight.sieveSectionsMap S F cS hcS cU hcU).toTruncated)) := by
  let eS := SetWeight.tensorSpaceFunctor_setWeightHomNatural S.functor hE M F cS hcS
  let eU := SetWeight.tensorSpaceFunctor_setWeightHomNatural (yoneda.obj U) hE M F cU hcU
  have h := sieveTensorSections_shapeIso S hE M F cS hcS cU hcU
  constructor
  · intro hp
    exact eU.isQCatEquivalence.cancel_left ((hp.comp eS.isQCatEquivalence).ofFunctorIso h)
  · intro hp
    exact eS.isQCatEquivalence.cancel_right ((eU.isQCatEquivalence.comp hp).ofFunctorIso h.symm)

end SerrePositivity.InfinityCategories.Sheaves
