module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.HomotopyRepresentations.IdentityCommaNormalizationHom
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.DGComposition.DGClosedHomWhiskerNaturality

/-! 実正規化 Hom の二射影は、augmentation の前後合成と同じ元の係数射影を回収する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded MonoidalCategory
variable (R : Type u) [CommRing R] (E : Type v) [DGCategory R E]
  (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R E E (DGFunctor.id E))

lemma dgGluingIdentityCommaPreNormalizeHom_source :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaPreNormalizeHom R E X Y ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSourceHomMap R E E (DGFunctor.id E)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E X.replacement) Y =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSourceHomMap R E E (DGFunctor.id E) X Y ≫
        eHomWhiskerRight (Complex R) X.augmentation (ForgetEnrichment.of (Complex R) Y.source) := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorHom_precompose (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSource R E E (DGFunctor.id E))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaNormalizationClosedIn R E X) (ForgetEnrichment.of (Complex R) Y)
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaNormalizationClosedIn_source] at h
  exact h

lemma dgGluingIdentityCommaPreNormalizeHom_replacement :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaPreNormalizeHom R E X Y ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacementHomMap R E E (DGFunctor.id E)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E X.replacement) Y =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacementHomMap R E E (DGFunctor.id E) X Y := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorHom_precompose (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacement R E E (DGFunctor.id E))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaNormalizationClosedIn R E X) (ForgetEnrichment.of (Complex R) Y)
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaNormalizationClosedIn_replacement] at h
  have hi := eHomWhiskerRight_id (Complex R) (ForgetEnrichment.of (Complex R) X.replacement)
    (ForgetEnrichment.of (Complex R) Y.replacement)
  exact h.trans ((congrArg (fun q => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacementHomMap R E E (DGFunctor.id E) X Y ≫ q)
    hi).trans (Category.comp_id _))

lemma dgGluingIdentityCommaPostNormalizeHom_source :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaPostNormalizeHom R E X Y ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSourceHomMap R E E (DGFunctor.id E)
          X (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E Y.source) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSourceHomMap R E E (DGFunctor.id E) X Y := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorHom_postcompose (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSource R E E (DGFunctor.id E))
    (ForgetEnrichment.of (Complex R) X) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaNormalizationClosedOut R E Y)
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaNormalizationClosedOut_source] at h
  have hi := eHomWhiskerLeft_id (Complex R) (ForgetEnrichment.of (Complex R) X.source)
    (ForgetEnrichment.of (Complex R) Y.source)
  exact h.trans ((congrArg (fun q => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSourceHomMap R E E (DGFunctor.id E) X Y ≫ q)
    hi).trans (Category.comp_id _))

lemma dgGluingIdentityCommaPostNormalizeHom_replacement :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaPostNormalizeHom R E X Y ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacementHomMap R E E (DGFunctor.id E)
          X (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E Y.source) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacementHomMap R E E (DGFunctor.id E) X Y ≫
        eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) X.replacement)
          Y.augmentation := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorHom_postcompose (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacement R E E (DGFunctor.id E))
    (ForgetEnrichment.of (Complex R) X) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaNormalizationClosedOut R E Y)
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaNormalizationClosedOut_replacement] at h
  exact h

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
