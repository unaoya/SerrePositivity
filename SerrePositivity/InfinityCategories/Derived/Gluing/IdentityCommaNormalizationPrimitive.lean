module
public import SerrePositivity.InfinityCategories.Derived.Gluing.IdentityCommaNormalizationProjections
public import SerrePositivity.InfinityCategories.Derived.EnrichedCochainUnit

/-! 実標準閉射での正規化前後合成は、零 primitive の項を消し、元の全比較 cochain を回収する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded MonoidalCategory CochainComplex HomComplex
variable (R : Type u) [CommRing R] (E : Type v) [DGCategory R E]
  (X Y : DGFunctorCommaObject R E E (DGFunctor.id E))

abbrev dgGluingIdentityCommaPreNormalizeInsertion :
    dgFunctorCommaHomComplex R E E (DGFunctor.id E) X Y ⟶
      dgFunctorCommaHomComplex R E E (DGFunctor.id E)
          (dgGluingIdentityCommaObject R E X.replacement) X ⊗
        dgFunctorCommaHomComplex R E E (DGFunctor.id E) X Y :=
  (λ_ _).inv ≫ dgGluingIdentityCommaNormalizationIn R E X ▷ _

abbrev dgGluingIdentityCommaPostNormalizeInsertion :
    dgFunctorCommaHomComplex R E E (DGFunctor.id E) X Y ⟶
      dgFunctorCommaHomComplex R E E (DGFunctor.id E) X Y ⊗
        dgFunctorCommaHomComplex R E E (DGFunctor.id E) Y
          (dgGluingIdentityCommaObject R E Y.source) :=
  (ρ_ _).inv ≫ _ ◁ dgGluingIdentityCommaNormalizationOut R E Y

lemma dgGluingIdentityCommaPreNormalize_firstPrimitive :
    (Cochain.ofHom (dgGluingIdentityCommaPreNormalizeInsertion R E X Y)).comp
      (dgFunctorCommaFirstCompositePrimitive R E E (DGFunctor.id E)
        (dgGluingIdentityCommaObject R E X.replacement) X Y) (zero_add (-1)) = 0 := by
  rw [dgFunctorCommaFirstCompositePrimitive, ← Cochain.comp_assoc_of_first_is_zero_cochain]
  rw [dgGluingIdentityCommaPreNormalizeInsertion,
    complexLeftUnitInsertion_rightTensor_zero _ _ _
      (dgGluingIdentityCommaNormalizationIn_primitive R E X),
    Cochain.zero_comp]

lemma dgGluingIdentityCommaPreNormalize_secondPrimitive :
    (Cochain.ofHom (dgGluingIdentityCommaPreNormalizeInsertion R E X Y)).comp
      (dgFunctorCommaSecondCompositePrimitive R E E (DGFunctor.id E)
        (dgGluingIdentityCommaObject R E X.replacement) X Y) (zero_add (-1)) =
      dgFunctorCommaPrimitive R E E (DGFunctor.id E) X Y := by
  rw [dgFunctorCommaSecondCompositePrimitive, dgGluingIdentityCommaPreNormalizeInsertion]
  exact enrichedCochain_leftUnit (R := R) E X.replacement Y.source
    (dgGluingIdentityCommaNormalizationIn R E X)
    (dgFunctorCommaReplacementHomMap R E E (DGFunctor.id E)
      (dgGluingIdentityCommaObject R E X.replacement) X)
    (dgGluingIdentityCommaNormalizationIn_replacement R E X) (-1)
    (dgFunctorCommaPrimitive R E E (DGFunctor.id E) X Y)

lemma dgGluingIdentityCommaNormalizationOut_image :
    dgGluingIdentityCommaNormalizationOut R E Y ≫
      dgFunctorCommaImageHomMap R E E (DGFunctor.id E) Y
        (dgGluingIdentityCommaObject R E Y.source) = eId (Complex R) Y.source := by
  change dgGluingIdentityCommaNormalizationOut R E Y ≫
    (dgFunctorCommaSourceHomMap R E E (DGFunctor.id E) _ _ ≫ 𝟙 _) = _
  rw [Category.comp_id, dgGluingIdentityCommaNormalizationOut_source]

lemma dgGluingIdentityCommaPostNormalize_firstPrimitive :
    (Cochain.ofHom (dgGluingIdentityCommaPostNormalizeInsertion R E X Y)).comp
      (dgFunctorCommaFirstCompositePrimitive R E E (DGFunctor.id E)
        X Y (dgGluingIdentityCommaObject R E Y.source)) (zero_add (-1)) =
      dgFunctorCommaPrimitive R E E (DGFunctor.id E) X Y := by
  rw [dgFunctorCommaFirstCompositePrimitive, dgGluingIdentityCommaPostNormalizeInsertion]
  exact enrichedCochain_rightUnit (R := R) E X.replacement Y.source
    (dgGluingIdentityCommaNormalizationOut R E Y)
    (dgFunctorCommaImageHomMap R E E (DGFunctor.id E) Y
      (dgGluingIdentityCommaObject R E Y.source))
    (dgGluingIdentityCommaNormalizationOut_image R E Y) (-1)
    (dgFunctorCommaPrimitive R E E (DGFunctor.id E) X Y)

lemma dgGluingIdentityCommaPostNormalize_secondPrimitive :
    (Cochain.ofHom (dgGluingIdentityCommaPostNormalizeInsertion R E X Y)).comp
      (dgFunctorCommaSecondCompositePrimitive R E E (DGFunctor.id E)
        X Y (dgGluingIdentityCommaObject R E Y.source)) (zero_add (-1)) = 0 := by
  rw [dgFunctorCommaSecondCompositePrimitive, ← Cochain.comp_assoc_of_first_is_zero_cochain]
  rw [dgGluingIdentityCommaPostNormalizeInsertion,
    complexRightUnitInsertion_leftTensor_zero _ _ _
      (dgGluingIdentityCommaNormalizationOut_primitive R E Y),
    Cochain.zero_comp]

lemma dgGluingIdentityCommaPreNormalizeHom_primitive :
    (Cochain.ofHom (dgGluingIdentityCommaPreNormalizeHom R E X Y)).comp
      (dgFunctorCommaPrimitive R E E (DGFunctor.id E)
        (dgGluingIdentityCommaObject R E X.replacement) Y) (zero_add (-1)) =
      dgFunctorCommaPrimitive R E E (DGFunctor.id E) X Y := by
  change dgFunctorCommaHomComparison R E E (DGFunctor.id E)
    (dgGluingIdentityCommaObject R E X.replacement) Y _
    (dgGluingIdentityCommaPreNormalizeInsertion R E X Y ≫
      dgFunctorCommaComposition R E E (DGFunctor.id E)
        (dgGluingIdentityCommaObject R E X.replacement) X Y) = _
  rw [dgFunctorCommaHomComparison_precompose, dgFunctorCommaComposition_comparison,
    dgFunctorCommaCompositePrimitive, Cochain.comp_add,
    dgGluingIdentityCommaPreNormalize_firstPrimitive,
    dgGluingIdentityCommaPreNormalize_secondPrimitive, zero_add]

lemma dgGluingIdentityCommaPostNormalizeHom_primitive :
    (Cochain.ofHom (dgGluingIdentityCommaPostNormalizeHom R E X Y)).comp
      (dgFunctorCommaPrimitive R E E (DGFunctor.id E)
        X (dgGluingIdentityCommaObject R E Y.source)) (zero_add (-1)) =
      dgFunctorCommaPrimitive R E E (DGFunctor.id E) X Y := by
  change dgFunctorCommaHomComparison R E E (DGFunctor.id E)
    X (dgGluingIdentityCommaObject R E Y.source) _
    (dgGluingIdentityCommaPostNormalizeInsertion R E X Y ≫
      dgFunctorCommaComposition R E E (DGFunctor.id E)
        X Y (dgGluingIdentityCommaObject R E Y.source)) = _
  rw [dgFunctorCommaHomComparison_precompose, dgFunctorCommaComposition_comparison,
    dgFunctorCommaCompositePrimitive, Cochain.comp_add,
    dgGluingIdentityCommaPostNormalize_firstPrimitive,
    dgGluingIdentityCommaPostNormalize_secondPrimitive, add_zero]

end SerrePositivity.InfinityCategories
