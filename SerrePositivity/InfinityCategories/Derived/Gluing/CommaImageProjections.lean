module
public import SerrePositivity.InfinityCategories.Derived.Gluing.CommaImageHom
public import SerrePositivity.InfinityCategories.Derived.DGFunctorCommaHomExt

/-! 標的恒等 comma への全 Hom 写像は、元の二射影・全比較 primitive を同じ実射として保持する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded CochainComplex HomComplex
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] (F : DGFunctor R C E)
  (X Y : DGFunctorCommaObject R C E F)

lemma dgGluingCommaImageHomMap_source :
    dgGluingCommaImageHomMap R C E F X Y ≫ dgFunctorCommaSourceHomMap R E E (DGFunctor.id E)
        (dgGluingCommaImageObject R C E F X) (dgGluingCommaImageObject R C E F Y) =
      dgFunctorCommaImageHomMap R C E F X Y :=
  dgFunctorCommaHomLift_source _ _ _ _ _ _ _ _ _ _ _

lemma dgGluingCommaImageHomMap_replacement :
    dgGluingCommaImageHomMap R C E F X Y ≫ dgFunctorCommaReplacementHomMap R E E (DGFunctor.id E)
        (dgGluingCommaImageObject R C E F X) (dgGluingCommaImageObject R C E F Y) =
      dgFunctorCommaReplacementHomMap R C E F X Y :=
  dgFunctorCommaHomLift_replacement _ _ _ _ _ _ _ _ _ _ _

lemma dgGluingCommaImageHomMap_primitive :
    (Cochain.ofHom (dgGluingCommaImageHomMap R C E F X Y)).comp
        (dgFunctorCommaPrimitive R E E (DGFunctor.id E) (dgGluingCommaImageObject R C E F X)
          (dgGluingCommaImageObject R C E F Y)) (zero_add (-1)) =
      dgFunctorCommaPrimitive R C E F X Y := by
  apply Cochain.ext
  intro p q hpq
  simp only [dgGluingCommaImageHomMap, dgFunctorCommaHomLift, dgFunctorCommaPrimitive,
    Cochain.zero_cochain_comp_v, Cochain.ofHom_v]
  exact mappingCocone.lift_f_snd_v _ _ _ _ p q hpq

lemma dgGluingCommaImageHomComparison (K : Complex R)
    (f : K ⟶ dgFunctorCommaHomComplex R C E F X Y) :
    dgFunctorCommaHomComparison R E E (DGFunctor.id E) (dgGluingCommaImageObject R C E F X)
        (dgGluingCommaImageObject R C E F Y) K (f ≫ dgGluingCommaImageHomMap R C E F X Y) =
      dgFunctorCommaHomComparison R C E F X Y K f := by
  change (Cochain.ofHom (f ≫ dgGluingCommaImageHomMap R C E F X Y)).comp
    (dgFunctorCommaPrimitive R E E (DGFunctor.id E) _ _) (zero_add (-1)) = _
  rw [Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain,
    dgGluingCommaImageHomMap_primitive]
  rfl

end SerrePositivity.InfinityCategories
