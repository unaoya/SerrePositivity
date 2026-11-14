module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.KernelComparisons.DGKernelCellSourceValue
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.KernelComparisons.DGKernelSourceRestrictionNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.SimplicialFunctors.FunctorIsoSourceEquivalenceSquare
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet DifferentialGraded MonoidalClosed
variable (R : Type u) [CommRing R] (D E : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
lemma dgKernelDerivedInfinity_cellSourceIso_hom_naturality
    {P0 P1 : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E D} (g : P0 ⟶ P1) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_cellSourceIso R D E
        (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D P0)).hom ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R (DGCategoryCellResolution.Source R D) E
          ((_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.augmentation R D).comp
            (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D P0)))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R (DGCategoryCellResolution.Source R D) E
          ((_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.augmentation R D).comp
            (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D P1)))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R D).inv
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor R (DGCategoryCellResolution.Source R D) E).map
          ((_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.middleLeftRestrictionFunctor R E D
            (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R D)
            (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.augmentation R D)).map g)) =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor R D E).map g ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_cellSourceIso R D E
        (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D P1)).hom := by
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_source_equivalence_square (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R D)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_sourceRestrictionIso R
      (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R D) D E (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.augmentation R D)
      (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D P0))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_sourceRestrictionIso R
      (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R D) D E (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.augmentation R D)
      (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D P1))
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor R D E).map g)
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor R (DGCategoryCellResolution.Source R D) E).map
      ((_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.middleLeftRestrictionFunctor R E D
        (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R D) (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.augmentation R D)).map g))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_sourceRestrictionIso_hom_naturality R
      (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R D) D E (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.augmentation R D) g)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_cellSourceIso R D E (BimoduleCategory.underlying R E D P0))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_cellSourceIso R D E (BimoduleCategory.underlying R E D P1))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_cellSourceIso_heq R D E (BimoduleCategory.underlying R E D P0))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_cellSourceIso_heq R D E (BimoduleCategory.underlying R E D P1))
end SerrePositivity.InfinityCategories.Project.DerivedCategories
