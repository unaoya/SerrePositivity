module
public import SerrePositivity.KST.Fibration.CompletedTwoSection
public import SerrePositivity.KST.SConstruction.MultiRealizationEquivalence

/-! # 補完を忘れる元の射影と同じ切断の全正有限反復での同値性 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration

/-- 元の補完を忘れる射影と同じ完全切断を持つ、完全な安定圏同値。 -/
def completedTwoForgetEquivalence {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    StableModelEquivalence (completedTwoModel q) (composableWeakArrowModel q) where
  hom := completedTwoForget q
  inv := completedTwoSection q
  homInvIso := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorIsoOfTrivialKanFibration (completedTwoForget q).val _ _ (by
    change ((completedTwoForget q ≫ completedTwoSection q) ≫ completedTwoForget q).val =
      (𝟙 (completedTwoModel q) ≫ completedTwoForget q).val
    rw [Category.assoc, completedTwoSection_forget, Category.comp_id, Category.id_comp])
  invHomIso := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (completedTwoSection q ≫ completedTwoForget q).val
      (𝟙 (composableWeakArrowModel q).carrier)
    rw [completedTwoSection_forget]
    exact Iso.refl _

/-- 同じ元の切断は、全正有限反復で局所化同型。 -/
lemma completedTwoSection_multi_localized_isIso {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (r : ℕ) :
    IsIso (AnodyneHomotopy.anodyneQ.map
      ((multiRealizationFunctor (r + 1)).map (completedTwoSection q))) :=
  multiRealization_map_localized_isIso_of_equivalence r (completedTwoForgetEquivalence q).symm

end SerrePositivity.KST.Fibration
