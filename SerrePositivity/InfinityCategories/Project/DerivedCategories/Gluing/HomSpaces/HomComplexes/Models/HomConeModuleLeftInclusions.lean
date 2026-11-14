module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.HomComplexes.Models.HomConeModuleInclusions
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.HomotopyRepresentations.YonedaHomConeLeftInverse
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.StableStructure.YonedaConeEvaluation

/-! 左右の Hom 円錐の左包含を、実加群円錐の同じ全 Hom 左包含へ送る。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory CochainComplex HomComplex DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (X Y Z : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
  (f : ForgetEnrichment.of (Complex R) Y ⟶ ForgetEnrichment.of (Complex R) Z)
local notation "P" => ForgetEnrichment.of (Complex R) (representable R X.left)
local notation "Q" => ForgetEnrichment.of (Complex R) (representable R X.right)
local notation "lf" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeLeftArrow R C D M Y Z f
local notation "rf" => CategoryTheory.Functor.map
  (DGFunctor.onClosed (dgYoneda R D)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeRightArrow R C D M Y Z f)

omit [Small.{u} D] in
/-- 左 Hom 円錐の左包含は、元の Yoneda と同じ加群 Hom 円錐左包含の合成。 -/
lemma dgGluingHomConeLeftModuleIso_inl :
    (mappingCone.inl (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeLeftArrow R C D M X Y Z f)).comp
      (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeLeftModuleIso R C D M X Y Z f).hom)
      (add_zero (-1)) =
    (Cochain.ofHom (yonedaHom R C X.left Y.left)).comp
      (moduleHomConeLeftCochain R C P lf) (zero_add (-1)) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeLeftModuleIso, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeLeftSourceIso,
    Iso.trans_hom, Iso.symm_hom, Cochain.ofHom_comp,
    ← Cochain.comp_assoc_of_third_is_zero_cochain]
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeInl_eqToIso _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftArrow_evaluate R C D M X Y Z f).symm]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingYonedaHomCone_inl_inv R C X.left lf

/-- 右 Hom 円錐の左包含も、元の Yoneda と同じ加群 Hom 円錐左包含の合成。 -/
lemma dgGluingHomConeRightModuleIso_inl :
    (mappingCone.inl (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeRightArrow R C D M X Y Z f)).comp
      (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeRightModuleIso R C D M X Y Z f).hom)
      (add_zero (-1)) =
    (Cochain.ofHom (yonedaHom R D X.right Y.right)).comp
      (moduleHomConeLeftCochain R D Q rf) (zero_add (-1)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingYonedaConeIso_inl R D X.right Y.right Z.right
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRight R C D M).onClosed.map f)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
