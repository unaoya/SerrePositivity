module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.CommaPostHomotopy
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.CommaStrictLift

/-! 第三 cochain が零の閉 comma 射の後合成は、元の第三 cochain の実後合成そのもの。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory CochainComplex HomComplex DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] (F : DGFunctor R C E)
  (X Y Z : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F)
  (f : ForgetEnrichment.of (Complex R) Y ⟶ ForgetEnrichment.of (Complex R) Z)
  (hf : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComparison R C E F Y Z (𝟙_ (Complex R))
    (ForgetEnrichment.homTo (Complex R) f) = 0)

include hf in
/-- 閉射の第三 cochain が零なら、第二合成項に現れる同じ第三作用も零。 -/
lemma dgGluingCommaThirdAction_of_comparison_zero :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaThirdAction R C E F X Y Z f = 0 := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaThirdAction
  rw [Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain,
    ← Cochain.comp_assoc_of_first_is_zero_cochain
      (Cochain.ofHom ((homObject R E X.replacement Y.replacement) ◁
        ForgetEnrichment.homTo (Complex R) f)),
    ← tensorLeftHom_ofHom]
  erw [← tensorLeftHom_cochain_comp (homObject R E X.replacement Y.replacement)
    (𝟙_ (Complex R)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F Y Z)
    (homObject R E Y.replacement (F.obj Z.source)) 0 (-1) (-1) (zero_add (-1))
    (Cochain.ofHom (ForgetEnrichment.homTo (Complex R) f))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R C E F Y Z)]
  change (Cochain.ofHom _).comp
    (((tensorLeftHom (homObject R E X.replacement Y.replacement) (𝟙_ (Complex R))
      (homObject R E Y.replacement (F.obj Z.source))).f (-1)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComparison R C E F Y Z (𝟙_ (Complex R))
          (ForgetEnrichment.homTo (Complex R) f))).comp _ (add_zero (-1)))
    (zero_add (-1)) = 0
  rw [hf, map_zero, Cochain.zero_comp, Cochain.comp_zero]

include hf in
/-- 厳密な閉射による後合成の第三 cochain は、第一項だけで与えられる。 -/
lemma dgGluingCommaPost_of_comparison_zero :
    (Cochain.ofHom (eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) X) f)).comp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R C E F X Z) (zero_add (-1)) =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R C E F X Y).comp
      (Cochain.ofHom (eHomWhiskerLeft (Complex R)
        (ForgetEnrichment.of (Complex R) X.replacement)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaPostImageArrow R C E F Y Z f))) (add_zero (-1)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaPost_primitive, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaCompositePrimitive,
    Cochain.comp_add, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaPost_first, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaPost_second]
  change _ + (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacementHomMap R C E F X Y)).comp
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaThirdAction R C E F X Y Z f) (zero_add (-1)) = _
  rw [dgGluingCommaThirdAction_of_comparison_zero R C E F X Y Z f hf,
    Cochain.comp_zero, add_zero]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
