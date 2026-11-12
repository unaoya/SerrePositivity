module
public import Mathlib.CategoryTheory.Whiskering
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelCellLiftCategory
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelCellModelHomFunctor
/-!
概要：模型と augmentation の全ての可換四角形上で canonical 模型と一般模型を比較する。
方針：同じ二つの指定自然同型を合成し、canonical 対象での恒等比較を回収する。
規約：canonical な対象の選択を dg 射上の厳密関手としない。使われ方：模型選択の整合性。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet DifferentialGraded MonoidalClosed
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] (D E : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
def dgKernelCanonicalCellLiftObject (P : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E D) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelCellLiftCategory R D E where
  obj :=
    { left := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellModel R D E (BimoduleCategory.underlying R E D P)
      right := P
      hom := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellResolution R D E (BimoduleCategory.underlying R E D P)).π }
  property :=
    ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellModel_rightRelativeKFlat R D E (BimoduleCategory.underlying R E D P),
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellResolution R D E (BimoduleCategory.underlying R E D P)).quasiIso⟩
def dgKernelCellLiftCanonicalComparisonIso :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellLiftSourceFunctor R D E ⋙ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellModelFunctorHomFunctor R D E ≅
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellLiftModelHomFunctor R D E :=
  (Functor.isoWhiskerLeft (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellLiftSourceFunctor R D E)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellModelFunctorHomIso R D E)).symm ≪≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellLiftHomIso R D E
lemma dgKernelCellLiftCanonicalComparisonIso_app (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelCellLiftCategory R D E) :
    (dgKernelCellLiftCanonicalComparisonIso R D E).app X =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_cellModelIso R D E
        (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D X.obj.right)).symm ≪≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_cellModelLiftIso R D E
          X.obj.right X.obj.left X.obj.hom X.property.1 X.property.2 := rfl
lemma dgKernelCellLiftCanonicalComparisonIso_canonical (P : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E D) :
    (dgKernelCellLiftCanonicalComparisonIso R D E).app
        (dgKernelCanonicalCellLiftObject R D E P) =
      Iso.refl ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellModelFunctorHomFunctor R D E).obj P) := by
  rw [dgKernelCellLiftCanonicalComparisonIso_app]
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_cellModelIso R D E
      (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D P)).symm ≪≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_cellModelLiftIso R D E P
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellModel R D E (BimoduleCategory.underlying R E D P))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellResolution R D E (BimoduleCategory.underlying R E D P)).π
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellModel_rightRelativeKFlat R D E (BimoduleCategory.underlying R E D P))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellResolution R D E (BimoduleCategory.underlying R E D P)).quasiIso = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_cellModelLiftIso_canonical]
  exact Iso.symm_self_id _
end
end SerrePositivity.InfinityCategories.Project.DerivedCategories
