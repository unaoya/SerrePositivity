module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ComparisonModels.RepresentableModel

/-! 代表加群からの任意の実閉射を、同じ augmentation を持つ gluing 対象へ戻す。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (c : C) (d : D)
  (a : ForgetEnrichment.of (Complex R) (representable R c) ⟶
    ForgetEnrichment.of (Complex R) (M.rightAt d))

def dgGluingObjectOfModuleArrow : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M where
  left := c
  right := d
  gluing := cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) a ≫
    (dgYonedaIso R c (M.rightAt d)).hom)

lemma dgGluingObjectOfModuleArrow_augmentation :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingAugmentation R C D M (dgGluingObjectOfModuleArrow R C D M c d a) = a := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingAugmentation, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject.gluingMap, dgGluingObjectOfModuleArrow]
  rw [unitFromCycle_cycleFromUnit, Category.assoc, Iso.hom_inv_id,
    Category.comp_id, ForgetEnrichment.homOf_homTo]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
