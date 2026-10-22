module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomConeModuleInclusions
public import SerrePositivity.InfinityCategories.Derived.Gluing.YonedaHomConeLeftInverse
public import SerrePositivity.InfinityCategories.Derived.Gluing.YonedaConeEvaluation

/-! 左右の Hom 円錐の左包含を、実加群円錐の同じ全 Hom 左包含へ送る。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory CochainComplex HomComplex DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (X Y Z : DGGluingObject R C D M)
  (f : ForgetEnrichment.of (Complex R) Y ⟶ ForgetEnrichment.of (Complex R) Z)
local notation "P" => ForgetEnrichment.of (Complex R) (representable R X.left)
local notation "Q" => ForgetEnrichment.of (Complex R) (representable R X.right)
local notation "lf" => dgGluingConeLeftArrow R C D M Y Z f
local notation "rf" => CategoryTheory.Functor.map
  (DGFunctor.onClosed (dgYoneda R D)) (dgGluingConeRightArrow R C D M Y Z f)

omit [Small.{u} D] in
/-- 左 Hom 円錐の左包含は、元の Yoneda と同じ加群 Hom 円錐左包含の合成。 -/
lemma dgGluingHomConeLeftModuleIso_inl :
    (mappingCone.inl (dgGluingHomConeLeftArrow R C D M X Y Z f)).comp
      (Cochain.ofHom (dgGluingHomConeLeftModuleIso R C D M X Y Z f).hom)
      (add_zero (-1)) =
    (Cochain.ofHom (yonedaHom R C X.left Y.left)).comp
      (moduleHomConeLeftCochain R C P lf) (zero_add (-1)) := by
  simp only [dgGluingHomConeLeftModuleIso, dgGluingHomConeLeftSourceIso,
    Iso.trans_hom, Iso.symm_hom, Cochain.ofHom_comp,
    ← Cochain.comp_assoc_of_third_is_zero_cochain]
  rw [dgGluingConeInl_eqToIso _ _ (dgGluingLeftArrow_evaluate R C D M X Y Z f).symm]
  exact dgGluingYonedaHomCone_inl_inv R C X.left lf

/-- 右 Hom 円錐の左包含も、元の Yoneda と同じ加群 Hom 円錐左包含の合成。 -/
lemma dgGluingHomConeRightModuleIso_inl :
    (mappingCone.inl (dgGluingHomConeRightArrow R C D M X Y Z f)).comp
      (Cochain.ofHom (dgGluingHomConeRightModuleIso R C D M X Y Z f).hom)
      (add_zero (-1)) =
    (Cochain.ofHom (yonedaHom R D X.right Y.right)).comp
      (moduleHomConeLeftCochain R D Q rf) (zero_add (-1)) :=
  dgGluingYonedaConeIso_inl R D X.right Y.right Z.right
    ((dgGluingRight R C D M).onClosed.map f)

end SerrePositivity.InfinityCategories
