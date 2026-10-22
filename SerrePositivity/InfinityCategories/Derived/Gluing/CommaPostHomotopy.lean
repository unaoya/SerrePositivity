module
public import SerrePositivity.InfinityCategories.Derived.Gluing.CommaPostBottom
/-! 左包含上で後合成の比較 cochain を回収し、同じ第三成分の作用へ因子分解する。 -/
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

def dgGluingCommaThirdAction : Cochain (homObject R E X.replacement Y.replacement)
    (homObject R E X.replacement (F.obj Z.source)) (-1) :=
  (Cochain.ofHom ((ρ_ (homObject R E X.replacement Y.replacement)).inv ≫
    (homObject R E X.replacement Y.replacement) ◁ ForgetEnrichment.homTo (Complex R) f)).comp
    (((tensorLeftHom (homObject R E X.replacement Y.replacement)
      (dgFunctorCommaHomComplex R C E F Y Z)
      (homObject R E Y.replacement (F.obj Z.source))).f (-1)
        (dgFunctorCommaPrimitive R C E F Y Z)).comp
      (Cochain.ofHom (eComp (Complex R) X.replacement Y.replacement (F.obj Z.source)))
      (add_zero (-1))) (zero_add (-1))

lemma dgGluingCommaInl_primitive : (mappingCocone.inl (dgFunctorCommaDifference R C E F X Y)).comp
    (dgFunctorCommaPrimitive R C E F X Y) (zero_add (-1)) = 0 := by
  apply Cochain.ext
  intro p q hpq
  simp only [Cochain.zero_cochain_comp_v, Cochain.zero_v, dgFunctorCommaPrimitive,
    mappingCocone.inl_v_snd_v]

lemma dgGluingCommaInl_replacement : (mappingCocone.inl (dgFunctorCommaDifference R C E F X Y)).comp
    (Cochain.ofHom (dgFunctorCommaReplacementHomMap R C E F X Y)) (zero_add 0) =
    Cochain.ofHom biprod.snd := by
  apply Cochain.ext₀
  intro n
  simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v,
    dgFunctorCommaReplacementHomMap, HomologicalComplex.comp_f,
    ← Category.assoc, mappingCocone.inl_v_fst_f, Category.id_comp]

lemma dgGluingCommaInl_postFirst : (mappingCocone.inl (dgFunctorCommaDifference R C E F X Y)).comp
    ((Cochain.ofHom (dgGluingCommaPostInsertion R C E F X Y Z f)).comp
      (dgFunctorCommaFirstCompositePrimitive R C E F X Y Z) (zero_add (-1)))
    (zero_add (-1)) = 0 := by
  rw [dgGluingCommaPost_first, ← Cochain.comp_assoc_of_third_is_zero_cochain,
    dgGluingCommaInl_primitive, Cochain.zero_comp]

lemma dgGluingCommaInl_postSecond : (mappingCocone.inl (dgFunctorCommaDifference R C E F X Y)).comp
    ((Cochain.ofHom (dgGluingCommaPostInsertion R C E F X Y Z f)).comp
      (dgFunctorCommaSecondCompositePrimitive R C E F X Y Z) (zero_add (-1)))
    (zero_add (-1)) =
    (Cochain.ofHom biprod.snd).comp (dgGluingCommaThirdAction R C E F X Y Z f) (zero_add (-1)) := by
  rw [dgGluingCommaPost_second, ← Cochain.comp_assoc_of_first_is_zero_cochain,
    dgGluingCommaInl_replacement]
  rfl

lemma dgGluingCommaInl_post : (mappingCocone.inl (dgFunctorCommaDifference R C E F X Y)).comp
    ((Cochain.ofHom (eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) X) f)).comp
      (dgFunctorCommaPrimitive R C E F X Z) (zero_add (-1))) (zero_add (-1)) =
    (Cochain.ofHom biprod.snd).comp (dgGluingCommaThirdAction R C E F X Y Z f) (zero_add (-1)) := by
  rw [dgGluingCommaPost_primitive, dgFunctorCommaCompositePrimitive,
    Cochain.comp_add, Cochain.comp_add, dgGluingCommaInl_postFirst,
    dgGluingCommaInl_postSecond, zero_add]

end SerrePositivity.InfinityCategories
