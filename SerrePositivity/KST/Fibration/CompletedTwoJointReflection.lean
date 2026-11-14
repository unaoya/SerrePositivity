module
public import SerrePositivity.KST.Fibration.CompletedTwoSPullback
public import SerrePositivity.KST.Fibration.SJointReflection

/-! # 補完した二辺図式の実両射影の共同反映と全 S_n への移送 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Fibration

/-- 保持した第二辺の全補完と元の第一辺は、零対象と実押し出しを共同で反映する。 -/
lemma completedTwo_jointReflection {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    JointlyReflectsSData (completedTwoCofiber q).val (completedTwoFirst q).val where
  zero v hc hf := by
    have hn := (weakArrowCofiberEquivalence q).hom.property.1 _ hc
    change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex ((completedTwoCofiber q ≫
      (weakArrowCofiberEquivalence q).hom).val.app _ v) at hn
    rw [completedTwoCofiber_projection] at hn
    have hz := composableWeakArrow_isZeroVertex_of_components q
      ((completedTwoForget q).val.app _ v) hf hn
    exact (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isZeroVertex_iff_map_of_trivialKanFibration (completedTwoForget q).val v).2 hz
  pushout F hc hf := by
    have hn := (stableModelHom_preservesSConstructionData
      (weakArrowCofiberEquivalence q).hom).2 _ hc
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (F ≫ (completedTwoCofiber q ≫
      (weakArrowCofiberEquivalence q).hom).val) at hn
    rw [completedTwoCofiber_projection] at hn
    have hz := composableWeakArrow_isPushoutSquare_of_components q
      (F ≫ (completedTwoForget q).val) hf hn
    exact (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isPushoutSquare_iff_postcomp_trivialKanFibration (completedTwoForget q).val F).2 hz

/-- 全 S_n で、同じ元の二つの後合成射が零対象と実押し出しを共同で反映する。 -/
lemma completedTwo_sJointReflection {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (n : ℕ) :
    JointlyReflectsSData ((sEndofunctor n).map (completedTwoCofiber q)).val
      ((sEndofunctor n).map (completedTwoFirst q)).val :=
  (completedTwo_jointReflection q).sConstruction n

end SerrePositivity.KST.Fibration
