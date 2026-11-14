module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.StableStructure.ShiftObject

/-! シフト候補の augmentation と、元の同じ加群シフトの比較を全 dg 自然なホモトピーで結ぶ。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) (n : ℤ)
  (p : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingShiftRepresentative R C X.left n)
  (q : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingShiftRepresentative R D X.right n)

/-- 同じ左シフト代表射で augmentation を戻す正方形は、全加群ホモトピーで可換。 -/
lemma dgGluingShiftAugmentation_transport :
    Nonempty (ModuleHomotopy R C
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingShiftRepresentativeHom R C X.left n p ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingShiftAugmentation R C D M X n p q)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingShiftAugmentationCore R C D M X n q)) := by
  apply (moduleToHomotopy_map_eq_iff R C _ _).1
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingShiftAugmentation]
  simp only [Functor.map_comp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingShiftRepresentativeHom_map,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingShiftRepresentativeInv_map, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- 構成した実 gluing 対象自身の augmentation も、同じ移送ホモトピーを持つ。 -/
lemma dgGluingShiftObject_augmentation_transport :
    Nonempty (ModuleHomotopy R C
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingShiftRepresentativeHom R C X.left n p ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingAugmentation R C D M
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingShiftObjectFromRepresentatives R C D M X n p q))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingShiftAugmentationCore R C D M X n q)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingShiftObject_augmentation]
  exact dgGluingShiftAugmentation_transport R C D M X n p q

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
