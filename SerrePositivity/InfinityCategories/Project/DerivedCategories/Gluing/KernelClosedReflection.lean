module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.KernelFunctor

/-! kernel 表示の同じ対象間の閉射を、全 Hom 鎖同型の逆で native gluing へ回収する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded MonoidalCategory
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)

/-- 同じ kernel 対象間の閉射を native Hom の実逆鎖写像で回収。 -/
def dgGluingKernelClosedPreimage
    (f : ForgetEnrichment.of (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelObject R C D M X) ⟶
      ForgetEnrichment.of (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelObject R C D M Y)) :
    ForgetEnrichment.of (Complex R) X ⟶ ForgetEnrichment.of (Complex R) Y :=
  ForgetEnrichment.homOf (Complex R)
    (ForgetEnrichment.homTo (Complex R) f ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelHomIso R C D M X Y).inv)

/-- 回収した閉射の像は、元の同じ kernel 閉射そのもの。 -/
lemma dgGluingKernelClosedPreimage_map
    (f : ForgetEnrichment.of (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelObject R C D M X) ⟶
      ForgetEnrichment.of (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelObject R C D M Y)) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToKernelComma R C D M).onClosed.map
      (dgGluingKernelClosedPreimage R C D M X Y f) = f := by
  apply (eHomEquiv (Complex R)).injective
  change ForgetEnrichment.homTo (Complex R)
    (dgGluingKernelClosedPreimage R C D M X Y f) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToKernelComma R C D M).map X Y = ForgetEnrichment.homTo (Complex R) f
  rw [dgGluingKernelClosedPreimage, ForgetEnrichment.homTo_homOf,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToKernelComma_map, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- native 閉射を送って回収すると、元の閉射に厳密に戻る。 -/
lemma dgGluingKernelClosedPreimage_of_map
    (f : ForgetEnrichment.of (Complex R) X ⟶ ForgetEnrichment.of (Complex R) Y) :
    dgGluingKernelClosedPreimage R C D M X Y
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToKernelComma R C D M).onClosed.map f) = f := by
  unfold dgGluingKernelClosedPreimage
  change ForgetEnrichment.homOf (Complex R)
    ((ForgetEnrichment.homTo (Complex R) f ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToKernelComma R C D M).map X Y) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelHomIso R C D M X Y).inv) = f
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToKernelComma_map, Category.assoc, Iso.hom_inv_id, Category.comp_id,
    ForgetEnrichment.homOf_homTo]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
