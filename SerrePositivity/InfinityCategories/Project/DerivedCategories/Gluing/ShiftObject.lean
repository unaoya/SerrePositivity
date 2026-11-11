module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.KernelShiftObject
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ShiftRepresentativeMaps

/-! 両側の整数シフト代表と同じ kernel augmentation から、実 gluing 対象を構成する。 -/
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
local notation "F" => Morita.kernelTensor R D C M

/-- 左のシフト加群を始域に保つ、同じ右代表への実 augmentation。 -/
def dgGluingShiftAugmentationCore :
    ForgetEnrichment.of (Complex R) (shiftModule n (representable R X.left)) ⟶
      ForgetEnrichment.of (Complex R) (M.rightAt q.obj) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelShiftAugmentation R C D M X n ≫
    (F).onClosed.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingShiftRepresentativeHom R D X.right n q) ≫
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelColumnIso R C D M (ForgetEnrichment.of (Complex R) q.obj)).hom

/-- 選んだ左右シフト代表を結ぶ、同じ augmentation の実閉移送。 -/
def dgGluingShiftAugmentation :
    ForgetEnrichment.of (Complex R) (representable R p.obj) ⟶
      ForgetEnrichment.of (Complex R) (M.rightAt q.obj) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingShiftRepresentativeInv R C X.left n p ≫
    dgGluingShiftAugmentationCore R C D M X n q

/-- 同じ閉 augmentation の Yoneda 逆像を比較閉元に持つ、実 gluing シフト候補。 -/
def dgGluingShiftObjectFromRepresentatives : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M where
  left := p.obj
  right := q.obj
  gluing := cycleFromUnit _
    (ForgetEnrichment.homTo (Complex R) (dgGluingShiftAugmentation R C D M X n p q) ≫
      (dgYonedaIso R p.obj (M.rightAt q.obj)).hom)

/-- 選んだ実対象の augmentation は、移送した同じ実加群射を厳密に回収。 -/
lemma dgGluingShiftObject_augmentation :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingAugmentation R C D M
      (dgGluingShiftObjectFromRepresentatives R C D M X n p q) =
      dgGluingShiftAugmentation R C D M X n p q := by
  change unitFromCycle _ (cycleFromUnit _
    (ForgetEnrichment.homTo (Complex R) (dgGluingShiftAugmentation R C D M X n p q) ≫
      (dgYonedaIso R p.obj (M.rightAt q.obj)).hom)) ≫
      (dgYonedaIso R p.obj (M.rightAt q.obj)).inv = _
  rw [unitFromCycle_cycleFromUnit]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rfl

omit p q in
/-- 元の両圏の前三角性を明示入力として、同じ任意整数シフト候補を供給。 -/
def dgGluingShiftObject (hC : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R C) (hD : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R D) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M :=
  dgGluingShiftObjectFromRepresentatives R C D M X n
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingChooseShiftRepresentative R C X.left n hC)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingChooseShiftRepresentative R D X.right n hD)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
