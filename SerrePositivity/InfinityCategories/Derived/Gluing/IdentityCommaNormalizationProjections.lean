module
public import SerrePositivity.InfinityCategories.Derived.Gluing.IdentityCommaNormalizationHom
public import SerrePositivity.InfinityCategories.Derived.DGClosedHomWhiskerNaturality

/-! 実正規化 Hom の二射影は、augmentation の前後合成と同じ元の係数射影を回収する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded MonoidalCategory
variable (R : Type u) [CommRing R] (E : Type v) [DGCategory R E]
  (X Y : DGFunctorCommaObject R E E (DGFunctor.id E))

lemma dgGluingIdentityCommaPreNormalizeHom_source :
    dgGluingIdentityCommaPreNormalizeHom R E X Y ≫
        dgFunctorCommaSourceHomMap R E E (DGFunctor.id E)
          (dgGluingIdentityCommaObject R E X.replacement) Y =
      dgFunctorCommaSourceHomMap R E E (DGFunctor.id E) X Y ≫
        eHomWhiskerRight (Complex R) X.augmentation (ForgetEnrichment.of (Complex R) Y.source) := by
  have h := dgFunctorHom_precompose (dgFunctorCommaSource R E E (DGFunctor.id E))
    (dgGluingIdentityCommaNormalizationClosedIn R E X) (ForgetEnrichment.of (Complex R) Y)
  rw [dgGluingIdentityCommaNormalizationClosedIn_source] at h
  exact h

lemma dgGluingIdentityCommaPreNormalizeHom_replacement :
    dgGluingIdentityCommaPreNormalizeHom R E X Y ≫
        dgFunctorCommaReplacementHomMap R E E (DGFunctor.id E)
          (dgGluingIdentityCommaObject R E X.replacement) Y =
      dgFunctorCommaReplacementHomMap R E E (DGFunctor.id E) X Y := by
  have h := dgFunctorHom_precompose (dgFunctorCommaReplacement R E E (DGFunctor.id E))
    (dgGluingIdentityCommaNormalizationClosedIn R E X) (ForgetEnrichment.of (Complex R) Y)
  rw [dgGluingIdentityCommaNormalizationClosedIn_replacement] at h
  have hi := eHomWhiskerRight_id (Complex R) (ForgetEnrichment.of (Complex R) X.replacement)
    (ForgetEnrichment.of (Complex R) Y.replacement)
  exact h.trans ((congrArg (fun q => dgFunctorCommaReplacementHomMap R E E (DGFunctor.id E) X Y ≫ q)
    hi).trans (Category.comp_id _))

lemma dgGluingIdentityCommaPostNormalizeHom_source :
    dgGluingIdentityCommaPostNormalizeHom R E X Y ≫
        dgFunctorCommaSourceHomMap R E E (DGFunctor.id E)
          X (dgGluingIdentityCommaObject R E Y.source) =
      dgFunctorCommaSourceHomMap R E E (DGFunctor.id E) X Y := by
  have h := dgFunctorHom_postcompose (dgFunctorCommaSource R E E (DGFunctor.id E))
    (ForgetEnrichment.of (Complex R) X) (dgGluingIdentityCommaNormalizationClosedOut R E Y)
  rw [dgGluingIdentityCommaNormalizationClosedOut_source] at h
  have hi := eHomWhiskerLeft_id (Complex R) (ForgetEnrichment.of (Complex R) X.source)
    (ForgetEnrichment.of (Complex R) Y.source)
  exact h.trans ((congrArg (fun q => dgFunctorCommaSourceHomMap R E E (DGFunctor.id E) X Y ≫ q)
    hi).trans (Category.comp_id _))

lemma dgGluingIdentityCommaPostNormalizeHom_replacement :
    dgGluingIdentityCommaPostNormalizeHom R E X Y ≫
        dgFunctorCommaReplacementHomMap R E E (DGFunctor.id E)
          X (dgGluingIdentityCommaObject R E Y.source) =
      dgFunctorCommaReplacementHomMap R E E (DGFunctor.id E) X Y ≫
        eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) X.replacement)
          Y.augmentation := by
  have h := dgFunctorHom_postcompose (dgFunctorCommaReplacement R E E (DGFunctor.id E))
    (ForgetEnrichment.of (Complex R) X) (dgGluingIdentityCommaNormalizationClosedOut R E Y)
  rw [dgGluingIdentityCommaNormalizationClosedOut_replacement] at h
  exact h

end SerrePositivity.InfinityCategories
