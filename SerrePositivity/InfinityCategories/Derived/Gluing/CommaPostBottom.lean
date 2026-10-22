module
public import SerrePositivity.InfinityCategories.Derived.Gluing.CommaPostcomposition
/-! comma の後合成を右包含へ制限すると、元の像の射による後合成を回収する。 -/
@[expose] public section
open CategoryTheory Limits MonoidalCategory CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] (F : DGFunctor R C E)
  (X Y Z : DGFunctorCommaObject R C E F)
  (f : ForgetEnrichment.of (Complex R) Y ⟶ ForgetEnrichment.of (Complex R) Z)


lemma dgGluingCommaInr_primitive :
    ((mappingCocone.inr (dgFunctorCommaDifference R C E F X Y)).val).comp
      (dgFunctorCommaPrimitive R C E F X Y) (add_neg_cancel 1) =
    Cochain.ofHom (𝟙 (homObject R E X.replacement (F.obj Y.source))) := by
  apply Cochain.ext₀
  intro n
  simp only [dgFunctorCommaPrimitive,
    Cochain.comp_v (n₁ := 1) (n₂ := -1) (n₁₂ := 0) _ _ (add_neg_cancel 1)
      n (n + 1) n rfl (by omega), Cochain.ofHom_v, HomologicalComplex.id_f]
  exact mappingCocone.inr_v_snd_v _ n (n + 1) rfl

lemma dgGluingCommaInr_replacement :
    ((mappingCocone.inr (dgFunctorCommaDifference R C E F X Y)).val).comp
    (Cochain.ofHom (dgFunctorCommaReplacementHomMap R C E F X Y)) (add_zero 1) = 0 := by
  apply Cochain.ext
  intro p q hpq
  simp only [Cochain.comp_zero_cochain_v, Cochain.ofHom_v, Cochain.zero_v,
    dgFunctorCommaReplacementHomMap, HomologicalComplex.comp_f, ← Category.assoc,
    mappingCocone.inr_v_fst_f, zero_comp]

lemma dgGluingCommaInr_postFirst :
    ((mappingCocone.inr (dgFunctorCommaDifference R C E F X Y)).val).comp
    ((Cochain.ofHom (dgGluingCommaPostInsertion R C E F X Y Z f)).comp
      (dgFunctorCommaFirstCompositePrimitive R C E F X Y Z) (zero_add (-1)))
    (add_neg_cancel 1) =
    Cochain.ofHom (eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) X.replacement)
      (dgGluingCommaPostImageArrow R C E F Y Z f)) := by
  rw [dgGluingCommaPost_first, ← Cochain.comp_assoc_of_third_is_zero_cochain,
    dgGluingCommaInr_primitive, Cochain.id_comp]

lemma dgGluingCommaInr_postSecond :
    ((mappingCocone.inr (dgFunctorCommaDifference R C E F X Y)).val).comp
    ((Cochain.ofHom (dgGluingCommaPostInsertion R C E F X Y Z f)).comp
      (dgFunctorCommaSecondCompositePrimitive R C E F X Y Z) (zero_add (-1)))
    (add_neg_cancel 1) = 0 := by
  rw [dgGluingCommaPost_second, ← Cochain.comp_assoc_of_second_is_zero_cochain,
    dgGluingCommaInr_replacement, Cochain.zero_comp]

lemma dgGluingCommaInr_post :
    ((mappingCocone.inr (dgFunctorCommaDifference R C E F X Y)).val).comp
    ((Cochain.ofHom (dgGluingCommaPostInsertion R C E F X Y Z f)).comp
      (dgFunctorCommaCompositePrimitive R C E F X Y Z) (zero_add (-1)))
    (add_neg_cancel 1) =
    Cochain.ofHom (eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) X.replacement)
      (dgGluingCommaPostImageArrow R C E F Y Z f)) := by
  rw [dgFunctorCommaCompositePrimitive, Cochain.comp_add, Cochain.comp_add,
    dgGluingCommaInr_postFirst, dgGluingCommaInr_postSecond, add_zero]

lemma dgGluingCommaPost_primitive :
    (Cochain.ofHom (eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) X) f)).comp
      (dgFunctorCommaPrimitive R C E F X Z) (zero_add (-1)) =
    (Cochain.ofHom (dgGluingCommaPostInsertion R C E F X Y Z f)).comp
      (dgFunctorCommaCompositePrimitive R C E F X Y Z) (zero_add (-1)) := by
  change (Cochain.ofHom (dgGluingCommaPostInsertion R C E F X Y Z f ≫
    dgFunctorCommaComposition R C E F X Y Z)).comp _ _ = _
  rw [Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain]
  have he := dgFunctorCommaComposition_comparison R C E F X Y Z
  change (Cochain.ofHom (dgFunctorCommaComposition R C E F X Y Z)).comp
    (dgFunctorCommaPrimitive R C E F X Z) (zero_add (-1)) = _ at he
  rw [he]

lemma dgGluingCommaPost_bottom :
    ((mappingCocone.inr (dgFunctorCommaDifference R C E F X Y)).val).comp
    ((Cochain.ofHom (eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) X) f)).comp
      (dgFunctorCommaPrimitive R C E F X Z) (zero_add (-1))) (add_neg_cancel 1) =
    Cochain.ofHom (eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) X.replacement)
      (dgGluingCommaPostImageArrow R C E F Y Z f)) := by
  rw [dgGluingCommaPost_primitive]
  exact dgGluingCommaInr_post R C E F X Y Z f

end SerrePositivity.InfinityCategories
