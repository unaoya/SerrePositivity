module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithfulIso
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.EquivalenceFullyFaithful

/-! # 全写像空間の充満忠実性を、指定した前合成同値で検出する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.KST.Fibration
open SerrePositivity.InfinityCategories

/-- 前合成した同じ射が充満忠実なら、前合成同値の逆を用いて元の射も充満忠実。 -/
theorem fullyFaithful_of_precomp_equivalence {X Y Z : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] [Quasicategory Z]
    {f : X ⟶ Y} {g : Y ⟶ Z} (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence f)
    (hfg : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (f ≫ g)) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful g := by
  let e := hf.choose
  have h := e.symm.isFullyFaithful.comp hfg
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (e.inv ≫ (e.hom ≫ g)) at h
  have ht := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp e.invHomIso g).isFullyFaithful_iff
  simp only [Category.id_comp] at ht
  exact ht.mp (by simpa only [Category.assoc] using h)

end SerrePositivity.KST.Fibration
