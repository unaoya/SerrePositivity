module
public import SerrePositivity.InfinityCategories.Derived.Gluing.ShiftObject

/-! シフト候補の augmentation と、元の同じ加群シフトの比較を全 dg 自然なホモトピーで結ぶ。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (X : DGGluingObject R C D M) (n : ℤ)
  (p : DGGluingShiftRepresentative R C X.left n)
  (q : DGGluingShiftRepresentative R D X.right n)

/-- 同じ左シフト代表射で augmentation を戻す正方形は、全加群ホモトピーで可換。 -/
lemma dgGluingShiftAugmentation_transport :
    Nonempty (ModuleHomotopy R C
      (dgGluingShiftRepresentativeHom R C X.left n p ≫
        dgGluingShiftAugmentation R C D M X n p q)
      (dgGluingShiftAugmentationCore R C D M X n q)) := by
  apply (moduleToHomotopy_map_eq_iff R C _ _).1
  rw [dgGluingShiftAugmentation]
  simp only [Functor.map_comp, dgGluingShiftRepresentativeHom_map,
    dgGluingShiftRepresentativeInv_map, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- 構成した実 gluing 対象自身の augmentation も、同じ移送ホモトピーを持つ。 -/
lemma dgGluingShiftObject_augmentation_transport :
    Nonempty (ModuleHomotopy R C
      (dgGluingShiftRepresentativeHom R C X.left n p ≫
        dgGluingAugmentation R C D M
          (dgGluingShiftObjectFromRepresentatives R C D M X n p q))
      (dgGluingShiftAugmentationCore R C D M X n q)) := by
  rw [dgGluingShiftObject_augmentation]
  exact dgGluingShiftAugmentation_transport R C D M X n p q

end SerrePositivity.InfinityCategories
