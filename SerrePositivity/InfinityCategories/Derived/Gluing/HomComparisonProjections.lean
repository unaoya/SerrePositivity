module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomComparison

/-! 全 Hom の代表加群比較は元の二射影を保持する。 -/
@[expose] public section
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)
  (X Y : DGGluingObject R C D M)
lemma dgGluingHomRepresentableIso_right :
    (dgGluingHomRepresentableIso R C D M X Y).hom ≫
      dgFunctorCommaSourceHomMap R D (RightModule R C) M.toFunctor
        (dgGluingCommaObject R C D M X) (dgGluingCommaObject R C D M Y) =
      dgGluingRightHomMap R C D M X Y := by
  simp only [dgGluingHomRepresentableIso, complexMappingCoconeMapIso,
    dgFunctorCommaSourceHomMap, ← Category.assoc, complexMappingCoconeMap_fst]
  rw [Category.assoc, dgGluingHomComponentsIso_hom]
  erw [biprod.lift_fst]
  rfl
lemma dgGluingHomRepresentableIso_left :
    (dgGluingHomRepresentableIso R C D M X Y).hom ≫
      dgFunctorCommaReplacementHomMap R D (RightModule R C) M.toFunctor
        (dgGluingCommaObject R C D M X) (dgGluingCommaObject R C D M Y) =
      dgGluingLeftHomMap R C D M X Y ≫ yonedaHom R C X.left Y.left := by
  simp only [dgGluingHomRepresentableIso, complexMappingCoconeMapIso,
    dgFunctorCommaReplacementHomMap, ← Category.assoc, complexMappingCoconeMap_fst]
  rw [Category.assoc, dgGluingHomComponentsIso_hom]
  erw [biprod.lift_snd]
  rfl

end SerrePositivity.InfinityCategories
