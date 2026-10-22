module
public import Mathlib.CategoryTheory.Whiskering
public import SerrePositivity.InfinityCategories.Derived.DGKernelCellLiftCategory
public import SerrePositivity.InfinityCategories.Derived.DGKernelCellModelHomFunctor
/-!
概要：模型と augmentation の全ての可換四角形上で canonical 模型と一般模型を比較する。
方針：同じ二つの指定自然同型を合成し、canonical 対象での恒等比較を回収する。
規約：canonical な対象の選択を dg 射上の厳密関手としない。使われ方：模型選択の整合性。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded DGNerve MonoidalClosed
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] (D E : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
def dgKernelCanonicalCellLiftObject (P : BimoduleCategory R E D) :
    DGKernelCellLiftCategory R D E where
  obj :=
    { left := dgKernelCellModel R D E (BimoduleCategory.underlying R E D P)
      right := P
      hom := (dgKernelCellResolution R D E (BimoduleCategory.underlying R E D P)).π }
  property :=
    ⟨dgKernelCellModel_rightRelativeKFlat R D E (BimoduleCategory.underlying R E D P),
      (dgKernelCellResolution R D E (BimoduleCategory.underlying R E D P)).quasiIso⟩
def dgKernelCellLiftCanonicalComparisonIso :
    dgKernelCellLiftSourceFunctor R D E ⋙ dgKernelCellModelFunctorHomFunctor R D E ≅
      dgKernelCellLiftModelHomFunctor R D E :=
  (Functor.isoWhiskerLeft (dgKernelCellLiftSourceFunctor R D E)
    (dgKernelCellModelFunctorHomIso R D E)).symm ≪≫ dgKernelCellLiftHomIso R D E
lemma dgKernelCellLiftCanonicalComparisonIso_app (X : DGKernelCellLiftCategory R D E) :
    (dgKernelCellLiftCanonicalComparisonIso R D E).app X =
      (dgKernelDerivedInfinity_cellModelIso R D E
        (BimoduleCategory.underlying R E D X.obj.right)).symm ≪≫
        dgKernelDerivedInfinity_cellModelLiftIso R D E
          X.obj.right X.obj.left X.obj.hom X.property.1 X.property.2 := rfl
lemma dgKernelCellLiftCanonicalComparisonIso_canonical (P : BimoduleCategory R E D) :
    (dgKernelCellLiftCanonicalComparisonIso R D E).app
        (dgKernelCanonicalCellLiftObject R D E P) =
      Iso.refl ((dgKernelCellModelFunctorHomFunctor R D E).obj P) := by
  rw [dgKernelCellLiftCanonicalComparisonIso_app]
  change (dgKernelDerivedInfinity_cellModelIso R D E
      (BimoduleCategory.underlying R E D P)).symm ≪≫
      dgKernelDerivedInfinity_cellModelLiftIso R D E P
        (dgKernelCellModel R D E (BimoduleCategory.underlying R E D P))
        (dgKernelCellResolution R D E (BimoduleCategory.underlying R E D P)).π
        (dgKernelCellModel_rightRelativeKFlat R D E (BimoduleCategory.underlying R E D P))
        (dgKernelCellResolution R D E (BimoduleCategory.underlying R E D P)).quasiIso = _
  rw [dgKernelDerivedInfinity_cellModelLiftIso_canonical]
  exact Iso.symm_self_id _
end
end SerrePositivity.InfinityCategories
