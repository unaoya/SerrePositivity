module
public import SerrePositivity.InfinityCategories.Derived.Gluing.CommaPostHomotopy
public import SerrePositivity.InfinityCategories.Derived.Gluing.CommaStrictLift

/-! 第三 cochain が零の閉 comma 射の後合成は、元の第三 cochain の実後合成そのもの。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory CochainComplex HomComplex DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] (F : DGFunctor R C E)
  (X Y Z : DGFunctorCommaObject R C E F)
  (f : ForgetEnrichment.of (Complex R) Y ⟶ ForgetEnrichment.of (Complex R) Z)
  (hf : dgFunctorCommaHomComparison R C E F Y Z (𝟙_ (Complex R))
    (ForgetEnrichment.homTo (Complex R) f) = 0)

include hf in
/-- 閉射の第三 cochain が零なら、第二合成項に現れる同じ第三作用も零。 -/
lemma dgGluingCommaThirdAction_of_comparison_zero :
    dgGluingCommaThirdAction R C E F X Y Z f = 0 := by
  unfold dgGluingCommaThirdAction
  rw [Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain,
    ← Cochain.comp_assoc_of_first_is_zero_cochain
      (Cochain.ofHom ((homObject R E X.replacement Y.replacement) ◁
        ForgetEnrichment.homTo (Complex R) f)),
    ← tensorLeftHom_ofHom]
  erw [← tensorLeftHom_cochain_comp (homObject R E X.replacement Y.replacement)
    (𝟙_ (Complex R)) (dgFunctorCommaHomComplex R C E F Y Z)
    (homObject R E Y.replacement (F.obj Z.source)) 0 (-1) (-1) (zero_add (-1))
    (Cochain.ofHom (ForgetEnrichment.homTo (Complex R) f))
    (dgFunctorCommaPrimitive R C E F Y Z)]
  change (Cochain.ofHom _).comp
    (((tensorLeftHom (homObject R E X.replacement Y.replacement) (𝟙_ (Complex R))
      (homObject R E Y.replacement (F.obj Z.source))).f (-1)
        (dgFunctorCommaHomComparison R C E F Y Z (𝟙_ (Complex R))
          (ForgetEnrichment.homTo (Complex R) f))).comp _ (add_zero (-1)))
    (zero_add (-1)) = 0
  rw [hf, map_zero, Cochain.zero_comp, Cochain.comp_zero]

include hf in
/-- 厳密な閉射による後合成の第三 cochain は、第一項だけで与えられる。 -/
lemma dgGluingCommaPost_of_comparison_zero :
    (Cochain.ofHom (eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) X) f)).comp
      (dgFunctorCommaPrimitive R C E F X Z) (zero_add (-1)) =
    (dgFunctorCommaPrimitive R C E F X Y).comp
      (Cochain.ofHom (eHomWhiskerLeft (Complex R)
        (ForgetEnrichment.of (Complex R) X.replacement)
        (dgGluingCommaPostImageArrow R C E F Y Z f))) (add_zero (-1)) := by
  rw [dgGluingCommaPost_primitive, dgFunctorCommaCompositePrimitive,
    Cochain.comp_add, dgGluingCommaPost_first, dgGluingCommaPost_second]
  change _ + (Cochain.ofHom (dgFunctorCommaReplacementHomMap R C E F X Y)).comp
    (dgGluingCommaThirdAction R C E F X Y Z f) (zero_add (-1)) = _
  rw [dgGluingCommaThirdAction_of_comparison_zero R C E F X Y Z f hf,
    Cochain.comp_zero, add_zero]

end SerrePositivity.InfinityCategories
