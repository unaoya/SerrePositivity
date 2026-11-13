module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Comparison.LaxHomPullbackEquivalence
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.LaxPullbacks.LaxHomFaithfulnessCriterion
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Comparison.LaxComparisonEssentialSurjectivity
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithfulEquivalence
/-!
概要：元の dg gluing から導来加群圏上の lax pullback への正本比較は ∞ 圏の同値である。
方針：正本 Hom 比較の実逆射から充満忠実性を得て、既存の本質的全射性と合わせる。
規約：元対象・Hom 複体・両射影と augmentation の族を保持する。
使われ方：全試験関手の普遍性と安定 gluing の比較に用いる。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  (D : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] (M : _root_.SerrePositivity.DifferentialGraded.Bimodule R C D)
lemma dgGluingUniverseDerivedNerveLaxComparison_isFullyFaithful :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedNerveLaxComparison R C D M) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedNerveLaxComparison_fullyFaithful_iff R C D M).mpr
    (fun X Y => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomPullbackComparison_equivalence R C D M X Y)
lemma dgGluingUniverseDerivedNerveLaxComparison_isQCatEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedNerveLaxComparison R C D M) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.isQCatEquivalence_of_isFullyFaithful_of_isEssentiallySurjective _
    (dgGluingUniverseDerivedNerveLaxComparison_isFullyFaithful R C D M)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedNerveLaxComparison_isEssentiallySurjective R C D M)

def dgGluingUniverseDerivedNerveLaxEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence
      ((SSet.uliftFunctor.{max (u + 1) v w,max u v w}).obj
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullback (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedYoneda.{u,v,w} R C)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedCoefficient R C D M)) :=
  (dgGluingUniverseDerivedNerveLaxComparison_isQCatEquivalence R C D M).choose
lemma dgGluingUniverseDerivedNerveLaxEquivalence_hom :
    (dgGluingUniverseDerivedNerveLaxEquivalence R C D M).hom =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedNerveLaxComparison R C D M := rfl
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
