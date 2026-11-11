module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.IdentityCommaNormalizationProjections
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.EnrichedCochainUnit

/-! 実標準閉射での正規化前後合成は、零 primitive の項を消し、元の全比較 cochain を回収する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded MonoidalCategory CochainComplex HomComplex
variable (R : Type u) [CommRing R] (E : Type v) [DGCategory R E]
  (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R E E (DGFunctor.id E))

abbrev dgGluingIdentityCommaPreNormalizeInsertion :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R E E (DGFunctor.id E) X Y ⟶
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R E E (DGFunctor.id E)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E X.replacement) X ⊗
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R E E (DGFunctor.id E) X Y :=
  (λ_ _).inv ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaNormalizationIn R E X ▷ _

abbrev dgGluingIdentityCommaPostNormalizeInsertion :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R E E (DGFunctor.id E) X Y ⟶
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R E E (DGFunctor.id E) X Y ⊗
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R E E (DGFunctor.id E) Y
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E Y.source) :=
  (ρ_ _).inv ≫ _ ◁ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaNormalizationOut R E Y

lemma dgGluingIdentityCommaPreNormalize_firstPrimitive :
    (Cochain.ofHom (dgGluingIdentityCommaPreNormalizeInsertion R E X Y)).comp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaFirstCompositePrimitive R E E (DGFunctor.id E)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E X.replacement) X Y) (zero_add (-1)) = 0 := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaFirstCompositePrimitive, ← Cochain.comp_assoc_of_first_is_zero_cochain]
  rw [dgGluingIdentityCommaPreNormalizeInsertion,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexLeftUnitInsertion_rightTensor_zero _ _ _
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaNormalizationIn_primitive R E X),
    Cochain.zero_comp]

lemma dgGluingIdentityCommaPreNormalize_secondPrimitive :
    (Cochain.ofHom (dgGluingIdentityCommaPreNormalizeInsertion R E X Y)).comp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSecondCompositePrimitive R E E (DGFunctor.id E)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E X.replacement) X Y) (zero_add (-1)) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R E E (DGFunctor.id E) X Y := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSecondCompositePrimitive, dgGluingIdentityCommaPreNormalizeInsertion]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.enrichedCochain_leftUnit (R := R) E X.replacement Y.source
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaNormalizationIn R E X)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacementHomMap R E E (DGFunctor.id E)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E X.replacement) X)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaNormalizationIn_replacement R E X) (-1)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R E E (DGFunctor.id E) X Y)

lemma dgGluingIdentityCommaNormalizationOut_image :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaNormalizationOut R E Y ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaImageHomMap R E E (DGFunctor.id E) Y
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E Y.source) = eId (Complex R) Y.source := by
  change _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaNormalizationOut R E Y ≫
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSourceHomMap R E E (DGFunctor.id E) _ _ ≫ 𝟙 _) = _
  rw [Category.comp_id, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaNormalizationOut_source]

lemma dgGluingIdentityCommaPostNormalize_firstPrimitive :
    (Cochain.ofHom (dgGluingIdentityCommaPostNormalizeInsertion R E X Y)).comp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaFirstCompositePrimitive R E E (DGFunctor.id E)
        X Y (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E Y.source)) (zero_add (-1)) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R E E (DGFunctor.id E) X Y := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaFirstCompositePrimitive, dgGluingIdentityCommaPostNormalizeInsertion]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.enrichedCochain_rightUnit (R := R) E X.replacement Y.source
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaNormalizationOut R E Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaImageHomMap R E E (DGFunctor.id E) Y
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E Y.source))
    (dgGluingIdentityCommaNormalizationOut_image R E Y) (-1)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R E E (DGFunctor.id E) X Y)

lemma dgGluingIdentityCommaPostNormalize_secondPrimitive :
    (Cochain.ofHom (dgGluingIdentityCommaPostNormalizeInsertion R E X Y)).comp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSecondCompositePrimitive R E E (DGFunctor.id E)
        X Y (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E Y.source)) (zero_add (-1)) = 0 := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSecondCompositePrimitive, ← Cochain.comp_assoc_of_first_is_zero_cochain]
  rw [dgGluingIdentityCommaPostNormalizeInsertion,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexRightUnitInsertion_leftTensor_zero _ _ _
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaNormalizationOut_primitive R E Y),
    Cochain.zero_comp]

lemma dgGluingIdentityCommaPreNormalizeHom_primitive :
    (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaPreNormalizeHom R E X Y)).comp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R E E (DGFunctor.id E)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E X.replacement) Y) (zero_add (-1)) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R E E (DGFunctor.id E) X Y := by
  change _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComparison R E E (DGFunctor.id E)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E X.replacement) Y _
    (dgGluingIdentityCommaPreNormalizeInsertion R E X Y ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaComposition R E E (DGFunctor.id E)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E X.replacement) X Y) = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComparison_precompose, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaComposition_comparison,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaCompositePrimitive, Cochain.comp_add,
    dgGluingIdentityCommaPreNormalize_firstPrimitive,
    dgGluingIdentityCommaPreNormalize_secondPrimitive, zero_add]

lemma dgGluingIdentityCommaPostNormalizeHom_primitive :
    (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaPostNormalizeHom R E X Y)).comp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R E E (DGFunctor.id E)
        X (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E Y.source)) (zero_add (-1)) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R E E (DGFunctor.id E) X Y := by
  change _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComparison R E E (DGFunctor.id E)
    X (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E Y.source) _
    (dgGluingIdentityCommaPostNormalizeInsertion R E X Y ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaComposition R E E (DGFunctor.id E)
        X Y (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E Y.source)) = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComparison_precompose, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaComposition_comparison,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaCompositePrimitive, Cochain.comp_add,
    dgGluingIdentityCommaPostNormalize_firstPrimitive,
    dgGluingIdentityCommaPostNormalize_secondPrimitive, add_zero]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
