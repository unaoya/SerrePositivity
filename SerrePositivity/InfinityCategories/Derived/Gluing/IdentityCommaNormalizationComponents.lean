module
public import SerrePositivity.InfinityCategories.Derived.Gluing.IdentityCommaNormalizationEdges

/-! 標準正規化閉射の二射影と比較 primitive は、augmentation・恒等射・厳密な零を回収する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded MonoidalCategory CochainComplex HomComplex
variable (R : Type u) [CommRing R] (E : Type v) [DGCategory R E]
  (X : DGFunctorCommaObject R E E (DGFunctor.id E))

lemma dgGluingIdentityCommaNormalizationIn_source :
    dgGluingIdentityCommaNormalizationIn R E X ≫ dgFunctorCommaSourceHomMap R E E (DGFunctor.id E)
        (dgGluingIdentityCommaObject R E X.replacement) X =
      ForgetEnrichment.homTo (Complex R) X.augmentation :=
  dgFunctorCommaHomLift_source _ _ _ _ _ _ _ _ _ _ _

lemma dgGluingIdentityCommaNormalizationIn_replacement :
    dgGluingIdentityCommaNormalizationIn R E X ≫
        dgFunctorCommaReplacementHomMap R E E (DGFunctor.id E)
          (dgGluingIdentityCommaObject R E X.replacement) X = eId (Complex R) X.replacement :=
  dgFunctorCommaHomLift_replacement _ _ _ _ _ _ _ _ _ _ _

lemma dgGluingIdentityCommaNormalizationOut_source :
    dgGluingIdentityCommaNormalizationOut R E X ≫ dgFunctorCommaSourceHomMap R E E (DGFunctor.id E)
        X (dgGluingIdentityCommaObject R E X.source) = eId (Complex R) X.source :=
  dgFunctorCommaHomLift_source _ _ _ _ _ _ _ _ _ _ _

lemma dgGluingIdentityCommaNormalizationOut_replacement :
    dgGluingIdentityCommaNormalizationOut R E X ≫
        dgFunctorCommaReplacementHomMap R E E (DGFunctor.id E)
          X (dgGluingIdentityCommaObject R E X.source) =
      ForgetEnrichment.homTo (Complex R) X.augmentation :=
  dgFunctorCommaHomLift_replacement _ _ _ _ _ _ _ _ _ _ _

lemma dgGluingIdentityCommaNormalizationIn_primitive :
    (Cochain.ofHom (dgGluingIdentityCommaNormalizationIn R E X)).comp
        (dgFunctorCommaPrimitive R E E (DGFunctor.id E)
          (dgGluingIdentityCommaObject R E X.replacement) X) (zero_add (-1)) = 0 := by
  apply Cochain.ext
  intro p q hpq
  simp only [dgGluingIdentityCommaNormalizationIn, dgFunctorCommaHomLift, dgFunctorCommaPrimitive,
    Cochain.zero_cochain_comp_v, Cochain.ofHom_v]
  exact mappingCocone.lift_f_snd_v _ _ _ _ p q hpq

lemma dgGluingIdentityCommaNormalizationOut_primitive :
    (Cochain.ofHom (dgGluingIdentityCommaNormalizationOut R E X)).comp
        (dgFunctorCommaPrimitive R E E (DGFunctor.id E)
          X (dgGluingIdentityCommaObject R E X.source)) (zero_add (-1)) = 0 := by
  apply Cochain.ext
  intro p q hpq
  simp only [dgGluingIdentityCommaNormalizationOut, dgFunctorCommaHomLift, dgFunctorCommaPrimitive,
    Cochain.zero_cochain_comp_v, Cochain.ofHom_v]
  exact mappingCocone.lift_f_snd_v _ _ _ _ p q hpq

end SerrePositivity.InfinityCategories
