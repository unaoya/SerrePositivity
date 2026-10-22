module
public import SerrePositivity.InfinityCategories.Derived.DGKernelCellSourceComparison
/-!
概要：指定済みの cell 入出力比較を、その同じ値と任意射の四角形で照合する。
方針：同じ入力同値の指定逆・augmentation・元の全関手比較を保持する。
規約：原 kernel の平坦性を追加しない。使われ方：元の cell 模型比較の自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded DGNerve MonoidalClosed
variable (R : Type u) [CommRing R] (D E : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
lemma dgKernelDerivedInfinity_cellSourceIso_heq (P : Bimodule R E D) :
    HEq (dgKernelDerivedInfinity_cellSourceIso R D E P)
      ((FunctorIso.postcomp (dgCellModuleSourceEquivalence R D).invHomIso
        (dgKernelDerivedInfinity R D E P)).symm ≪≫
        FunctorIso.precomp
          (dgKernelDerivedInfinity_sourceRestrictionIso R
            (DGCategoryCellResolution.Source R D) D E
            (DGCategoryCellResolution.augmentation R D) P)
          (dgCellModuleSourceEquivalence R D).inv) := by
  simp only [dgKernelDerivedInfinity_cellSourceIso]
  rfl
end SerrePositivity.InfinityCategories
