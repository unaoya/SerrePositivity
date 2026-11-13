module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.IdentityComparisons.IdentityCommaGeneralDifference
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.HomotopyModels.EnrichedIdentityWhiskering

/-! 恒等 comma の任意 augmentation へ入る標準閉射と、そこから標的恒等 augmentation への標準閉射。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits DifferentialGraded MonoidalCategory CochainComplex HomComplex
variable (R : Type u) [CommRing R] (E : Type v) [DGCategory R E]
  (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R E E (DGFunctor.id E))

lemma dgGluingIdentityCommaNormalizationIn_difference :
    biprod.lift (ForgetEnrichment.homTo (Complex R) X.augmentation)
        (eId (Complex R) X.replacement) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaDifference R E E (DGFunctor.id E)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E X.replacement) X = 0 := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaGeneralDifference_lift R E
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E X.replacement) X (𝟙_ (Complex R))
    (ForgetEnrichment.homTo (Complex R) X.augmentation) (eId (Complex R) X.replacement)
  refine h.trans ?_
  let α : ForgetEnrichment.of (Complex R) X.replacement ⟶
      ForgetEnrichment.of (Complex R) X.source := X.augmentation
  have hp : ForgetEnrichment.homTo (Complex R) α ≫
      eHomWhiskerRight (Complex R) (𝟙 (ForgetEnrichment.of (Complex R) X.replacement))
        (ForgetEnrichment.of (Complex R) X.source) = ForgetEnrichment.homTo (Complex R) α := by
    rw [eHomWhiskerRight_id]
    exact Category.comp_id _
  have hq := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.enrichedIdentity_postcompose (Complex R) (ForgetEnrichment (Complex R) E) α
  convert sub_eq_zero.mpr (hp.trans hq.symm) using 1 <;> rfl

lemma dgGluingIdentityCommaNormalizationOut_difference :
    biprod.lift (eId (Complex R) X.source) (ForgetEnrichment.homTo (Complex R) X.augmentation) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaDifference R E E (DGFunctor.id E) X
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E X.source) = 0 := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaGeneralDifference_lift R E
    X (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E X.source) (𝟙_ (Complex R))
    (eId (Complex R) X.source) (ForgetEnrichment.homTo (Complex R) X.augmentation)
  refine h.trans ?_
  let α : ForgetEnrichment.of (Complex R) X.replacement ⟶
      ForgetEnrichment.of (Complex R) X.source := X.augmentation
  have hp := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.enrichedIdentity_precompose (Complex R) (ForgetEnrichment (Complex R) E) α
  have hq : ForgetEnrichment.homTo (Complex R) α ≫
      eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) X.replacement)
        (𝟙 (ForgetEnrichment.of (Complex R) X.source)) = ForgetEnrichment.homTo (Complex R) α := by
    have hi := eHomWhiskerLeft_id (Complex R)
      (ForgetEnrichment.of (Complex R) X.replacement) (ForgetEnrichment.of (Complex R) X.source)
    exact (congrArg (fun q => ForgetEnrichment.homTo (Complex R) α ≫ q) hi).trans
      (Category.comp_id _)
  convert sub_eq_zero.mpr (hp.trans hq.symm) using 1 <;> rfl

def dgGluingIdentityCommaNormalizationIn :
    𝟙_ (Complex R) ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R E E (DGFunctor.id E)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E X.replacement) X :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomLift R E E (DGFunctor.id E) _ _ _
    (ForgetEnrichment.homTo (Complex R) X.augmentation) (eId (Complex R) X.replacement) 0 (by
      rw [dgGluingIdentityCommaNormalizationIn_difference]
      simp)

def dgGluingIdentityCommaNormalizationOut :
    𝟙_ (Complex R) ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R E E (DGFunctor.id E) X
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E X.source) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomLift R E E (DGFunctor.id E) _ _ _
    (eId (Complex R) X.source) (ForgetEnrichment.homTo (Complex R) X.augmentation) 0 (by
      rw [dgGluingIdentityCommaNormalizationOut_difference]
      simp)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
