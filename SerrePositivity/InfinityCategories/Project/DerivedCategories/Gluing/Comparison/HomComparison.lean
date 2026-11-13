module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Functoriality.ActionYoneda
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.ComplexMappingCoconeMapIso

/-! 比較差の可換正方形を使い、元の全 Hom と代表加群表示の全 Hom を鎖同型で比較する。 -/
@[expose] public section
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)
  (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
def dgGluingHomComponentsIso :
    (homObject R C X.left Y.left ⊞ homObject R D X.right Y.right) ≅
      (homObject R D X.right Y.right ⊞
        moduleHom R C (representable R X.left) (representable R Y.left)) :=
  biprod.braiding _ _ ≪≫ biprod.mapIso (Iso.refl _)
    (dgYonedaIso R X.left (representable R Y.left)).symm
lemma dgGluingHomComponentsIso_hom :
    (dgGluingHomComponentsIso R C D M X Y).hom =
      biprod.lift biprod.snd (biprod.fst ≫ yonedaHom R C X.left Y.left) := by
  apply biprod.hom_ext <;>
    simp [dgGluingHomComponentsIso, biprod.braiding, yonedaHom]
lemma dgGluingHomDifference_yoneda :
    (dgGluingHomComponentsIso R C D M X Y).hom ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaDifference R D (RightModule R C) M.toFunctor
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M X) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M Y) ≫
      (dgYonedaIso R X.left (M.rightAt Y.right)).hom =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDifference R C D M X Y := by
  simp only [dgGluingHomComponentsIso_hom, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaDifference, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject,
    Preadditive.comp_sub, Preadditive.sub_comp, Category.assoc]
  erw [biprod.lift_fst_assoc, biprod.lift_snd_assoc]
  simp only [Category.assoc]
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightAction_yoneda, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftAction_yoneda]
  rfl

def dgGluingHomRepresentableIso : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComplex R C D M X Y ≅
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R D (RightModule R C) M.toFunctor
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M X) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M Y) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMapIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDifference R C D M X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaDifference R D (RightModule R C) M.toFunctor
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M X) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M Y))
    (dgGluingHomComponentsIso R C D M X Y) (dgYonedaIso R X.left (M.rightAt Y.right)).symm (by
      apply (cancel_mono (dgYonedaIso R X.left (M.rightAt Y.right)).hom).1
      simp only [Category.assoc, Iso.symm_hom, Iso.inv_hom_id, Category.comp_id]
      exact (dgGluingHomDifference_yoneda R C D M X Y).symm)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
