module

public import SerrePositivity.KST.LocalizingInvariants.TammeQuotientCandidate
public import SerrePositivity.KST.LocalizingInvariants.LocalizationUniqueness
public import SerrePositivity.KST.LocalizingInvariants.LaxDifferenceAdjunction
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.EquivalenceStability

/-!
概要：q が充満忠実な右随伴を持つ場合、一般商候補から元の E への比較は実同値。
方針：元の差も同じ辺集合の局所化なので、二つの局所化の比較の実逆を構成する。
規約：順方向は元の tammeQuotientComparison。使われ方：一般商と反射的な場合の整合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
variable {C D E : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D E)
  (v : E.obj ⟶ D.obj) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction q.hom v) (hv : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful v)

include a hv in
lemma tammeDifference_isLocalization :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization (laxDifference p q) (tammeLocalizingEdges p q) := by
  rw [tammeLocalizingEdges_eq]
  exact laxDifference_isLocalization p q v a hv

def tammeQuotientReflectiveEquivalence : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (tammeQuotient p q) E.obj :=
  localizationComparisonEquivalence (tammeQuotientMap p q) (laxDifference p q)
    (tammeLocalizingEdges p q) (tammeQuotient_isLocalization p q)
    (tammeDifference_isLocalization p q v a hv) (tammeQuotientComparison p q)
    (tammeQuotientComparisonIso p q)

include a hv in
lemma tammeQuotientComparison_isQCatEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (tammeQuotientComparison p q) :=
  (tammeQuotientReflectiveEquivalence p q v a hv).isQCatEquivalence

include a hv in
lemma tammeQuotient_isStable_of_reflective : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable (tammeQuotient p q) :=
  (tammeQuotientReflectiveEquivalence p q v a hv).isStable_iff.mpr inferInstance

end SerrePositivity.KST.LocalizingInvariants
