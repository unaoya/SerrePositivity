module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.IdentityComparisons.IdentityCommaNormalizationComponents
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.DGFunctors.DGFunctorCommaProjections

/-! 標準正規化射を同じ恒等 comma の実閉射として保持し、二つの dg 射影で厳密に回収する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded MonoidalCategory
variable (R : Type u) [CommRing R] (E : Type v) [DGCategory R E]
  (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R E E (DGFunctor.id E))

def dgGluingIdentityCommaNormalizationClosedIn :
    ForgetEnrichment.of (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E X.replacement) ⟶
      ForgetEnrichment.of (Complex R) X :=
  ForgetEnrichment.homOf (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaNormalizationIn R E X)

def dgGluingIdentityCommaNormalizationClosedOut :
    ForgetEnrichment.of (Complex R) X ⟶
      ForgetEnrichment.of (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E X.source) :=
  ForgetEnrichment.homOf (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaNormalizationOut R E X)

lemma dgGluingIdentityCommaNormalizationClosedIn_source :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSource R E E (DGFunctor.id E)).onClosed.map
        (dgGluingIdentityCommaNormalizationClosedIn R E X) = X.augmentation := by
  change _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaNormalizationIn R E X ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSourceHomMap R E E (DGFunctor.id E) _ _ = _
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaNormalizationIn_source R E X

lemma dgGluingIdentityCommaNormalizationClosedIn_replacement :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacement R E E (DGFunctor.id E)).onClosed.map
        (dgGluingIdentityCommaNormalizationClosedIn R E X) =
      𝟙 (ForgetEnrichment.of (Complex R) X.replacement) := by
  change _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaNormalizationIn R E X ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacementHomMap R E E (DGFunctor.id E) _ _ = _
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaNormalizationIn_replacement R E X

lemma dgGluingIdentityCommaNormalizationClosedOut_source :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSource R E E (DGFunctor.id E)).onClosed.map
        (dgGluingIdentityCommaNormalizationClosedOut R E X) =
      𝟙 (ForgetEnrichment.of (Complex R) X.source) := by
  change _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaNormalizationOut R E X ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSourceHomMap R E E (DGFunctor.id E) _ _ = _
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaNormalizationOut_source R E X

lemma dgGluingIdentityCommaNormalizationClosedOut_replacement :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacement R E E (DGFunctor.id E)).onClosed.map
        (dgGluingIdentityCommaNormalizationClosedOut R E X) = X.augmentation := by
  change _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaNormalizationOut R E X ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacementHomMap R E E (DGFunctor.id E) _ _ = _
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaNormalizationOut_replacement R E X

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
