module
public import SerrePositivity.InfinityCategories.Derived.Gluing.IdentityCommaNormalizationComponents
public import SerrePositivity.InfinityCategories.Derived.DGFunctorCommaProjections

/-! 標準正規化射を同じ恒等 comma の実閉射として保持し、二つの dg 射影で厳密に回収する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded MonoidalCategory
variable (R : Type u) [CommRing R] (E : Type v) [DGCategory R E]
  (X : DGFunctorCommaObject R E E (DGFunctor.id E))

def dgGluingIdentityCommaNormalizationClosedIn :
    ForgetEnrichment.of (Complex R) (dgGluingIdentityCommaObject R E X.replacement) ⟶
      ForgetEnrichment.of (Complex R) X :=
  ForgetEnrichment.homOf (Complex R) (dgGluingIdentityCommaNormalizationIn R E X)

def dgGluingIdentityCommaNormalizationClosedOut :
    ForgetEnrichment.of (Complex R) X ⟶
      ForgetEnrichment.of (Complex R) (dgGluingIdentityCommaObject R E X.source) :=
  ForgetEnrichment.homOf (Complex R) (dgGluingIdentityCommaNormalizationOut R E X)

lemma dgGluingIdentityCommaNormalizationClosedIn_source :
    (dgFunctorCommaSource R E E (DGFunctor.id E)).onClosed.map
        (dgGluingIdentityCommaNormalizationClosedIn R E X) = X.augmentation := by
  change dgGluingIdentityCommaNormalizationIn R E X ≫
    dgFunctorCommaSourceHomMap R E E (DGFunctor.id E) _ _ = _
  exact dgGluingIdentityCommaNormalizationIn_source R E X

lemma dgGluingIdentityCommaNormalizationClosedIn_replacement :
    (dgFunctorCommaReplacement R E E (DGFunctor.id E)).onClosed.map
        (dgGluingIdentityCommaNormalizationClosedIn R E X) =
      𝟙 (ForgetEnrichment.of (Complex R) X.replacement) := by
  change dgGluingIdentityCommaNormalizationIn R E X ≫
    dgFunctorCommaReplacementHomMap R E E (DGFunctor.id E) _ _ = _
  exact dgGluingIdentityCommaNormalizationIn_replacement R E X

lemma dgGluingIdentityCommaNormalizationClosedOut_source :
    (dgFunctorCommaSource R E E (DGFunctor.id E)).onClosed.map
        (dgGluingIdentityCommaNormalizationClosedOut R E X) =
      𝟙 (ForgetEnrichment.of (Complex R) X.source) := by
  change dgGluingIdentityCommaNormalizationOut R E X ≫
    dgFunctorCommaSourceHomMap R E E (DGFunctor.id E) _ _ = _
  exact dgGluingIdentityCommaNormalizationOut_source R E X

lemma dgGluingIdentityCommaNormalizationClosedOut_replacement :
    (dgFunctorCommaReplacement R E E (DGFunctor.id E)).onClosed.map
        (dgGluingIdentityCommaNormalizationClosedOut R E X) = X.augmentation := by
  change dgGluingIdentityCommaNormalizationOut R E X ≫
    dgFunctorCommaReplacementHomMap R E E (DGFunctor.id E) _ _ = _
  exact dgGluingIdentityCommaNormalizationOut_replacement R E X

end SerrePositivity.InfinityCategories
