module
public import SerrePositivity.InfinityCategories.Derived.DGKernelCellSourceValue
public import SerrePositivity.InfinityCategories.Derived.DGKernelSourceRestrictionNaturality
public import SerrePositivity.InfinityCategories.Derived.FunctorIsoSourceEquivalenceSquare
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
lemma dgKernelDerivedInfinity_cellSourceIso_hom_naturality
    {P0 P1 : BimoduleCategory R E D} (g : P0 ⟶ P1) :
    (dgKernelDerivedInfinity_cellSourceIso R D E
        (BimoduleCategory.underlying R E D P0)).hom ≫
      functorHomPrecomp
        (dgKernelDerivedInfinity R (DGCategoryCellResolution.Source R D) E
          ((DGCategoryCellResolution.augmentation R D).comp
            (BimoduleCategory.underlying R E D P0)))
        (dgKernelDerivedInfinity R (DGCategoryCellResolution.Source R D) E
          ((DGCategoryCellResolution.augmentation R D).comp
            (BimoduleCategory.underlying R E D P1)))
        (dgCellModuleSourceEquivalence R D).inv
        ((dgKernelDerivedFunctorHomFunctor R (DGCategoryCellResolution.Source R D) E).map
          ((BimoduleCategory.middleLeftRestrictionFunctor R E D
            (DGCategoryCellResolution.Source R D)
            (DGCategoryCellResolution.augmentation R D)).map g)) =
    (dgKernelDerivedFunctorHomFunctor R D E).map g ≫
      (dgKernelDerivedInfinity_cellSourceIso R D E
        (BimoduleCategory.underlying R E D P1)).hom := by
  exact functorIso_source_equivalence_square (dgCellModuleSourceEquivalence R D)
    (dgKernelDerivedInfinity_sourceRestrictionIso R
      (DGCategoryCellResolution.Source R D) D E (DGCategoryCellResolution.augmentation R D)
      (BimoduleCategory.underlying R E D P0))
    (dgKernelDerivedInfinity_sourceRestrictionIso R
      (DGCategoryCellResolution.Source R D) D E (DGCategoryCellResolution.augmentation R D)
      (BimoduleCategory.underlying R E D P1))
    ((dgKernelDerivedFunctorHomFunctor R D E).map g)
    ((dgKernelDerivedFunctorHomFunctor R (DGCategoryCellResolution.Source R D) E).map
      ((BimoduleCategory.middleLeftRestrictionFunctor R E D
        (DGCategoryCellResolution.Source R D) (DGCategoryCellResolution.augmentation R D)).map g))
    (dgKernelDerivedInfinity_sourceRestrictionIso_hom_naturality R
      (DGCategoryCellResolution.Source R D) D E (DGCategoryCellResolution.augmentation R D) g)
    (dgKernelDerivedInfinity_cellSourceIso R D E (BimoduleCategory.underlying R E D P0))
    (dgKernelDerivedInfinity_cellSourceIso R D E (BimoduleCategory.underlying R E D P1))
    (dgKernelDerivedInfinity_cellSourceIso_heq R D E (BimoduleCategory.underlying R E D P0))
    (dgKernelDerivedInfinity_cellSourceIso_heq R D E (BimoduleCategory.underlying R E D P1))
end SerrePositivity.InfinityCategories
