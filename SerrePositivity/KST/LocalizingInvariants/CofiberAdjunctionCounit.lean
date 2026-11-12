module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberAdjunctionCounit

public import SerrePositivity.KST.LocalizingInvariants.CofiberRightAdjointFaithful
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.ReflectiveIdempotence

/-!
概要：元の cofiber の実随伴の余単位は可逆である。
方針：零始点矢印への関手同値と全部分圏包含に分解し、全関手圏で充満忠実性を示す。
規約：対象ごとの同型で代用しない。使われ方：差の関手の局所化普遍性への接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
attribute [local instance] _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.cofiberCounitZeroSourceQuasicategory
variable (X : SSet.{u}) [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]

lemma cofiberRightAdjointZeroSource_isQCatEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (cofiberRightAdjointZeroSource X) := by
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (cofiberRightAdjointZeroSource X ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroSourceArrowTarget X) := by
    rw [cofiberRightAdjointZeroSource_target]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence.refl X).isQCatEquivalence
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroSourceArrowTarget X)).cancel_right h

/-- 任意のパラメータの全関手圏でも元の右随伴による後合成は充満忠実。 -/
lemma cofiberRightAdjoint_postcomp_fullyFaithful (A : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful ((ihom A).map (cofiberRightAdjoint X)) := by
  have hs := ((cofiberRightAdjointZeroSource_isQCatEquivalence X).postcompose A).isFullyFaithful
  have h := hs.comp (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.isFullyFaithful_fullSubcomplexFunctorInclusion A
    ((ihom (Δ[1] : SSet.{u})).obj X) _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsZeroSourceArrow)
  rw [← CategoryTheory.Functor.map_comp, cofiberRightAdjointZeroSource_inclusion] at h
  exact h

lemma cofiberAdjunction_counitHom_isIso : IsIso (cofiberAdjunction X).counitHom :=
  (cofiberAdjunction X).counitHom_isIso_of_postcompFullyFaithful
    (cofiberRightAdjoint_postcomp_fullyFaithful X X).toHoFullyFaithful

lemma cofiberAdjunction_counit_isIso : IsIso (cofiberAdjunction X).counit := by
  have := cofiberAdjunction_counitHom_isIso X
  exact _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.counit_isIso_of_counitHom _

end SerrePositivity.KST.LocalizingInvariants
