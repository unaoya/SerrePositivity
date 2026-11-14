module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.KernelComparisons.DGKernelSourceRestrictionInfinity
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.Nerves.CellDGResolutionNerve
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CompactnessAndPresentability.DGModuleMoritaInfinity
/-!
概要：元の一般 kernel の実作用を、cell 分解上の作用と指定入力同値の逆へ比較する。
方針：cell 増大の実加群 ∞ 同値と、同じ graph 始域制限比較を使う。
規約：元の dg 圏に局所 Hom 平坦性を追加しない。
使われ方：一般導来合成の入力模型移送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
variable (R : Type u) [CommRing R] (D E : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
/-- cell 増大の実延長を順方向に持つ、実導来加群 ∞ 圏の同値。 -/
def dgCellModuleSourceEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R (DGCategoryCellResolution.Source R D))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleExtensionInfinity_isQCatEquivalence_of_quasiEquivalence R
    (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R D) D (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.augmentation R D)
    (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.augmentation_quasiEquivalence R D)).choose
/-- 指定入力同値の順方向は元の cell 増大の実延長そのもの。 -/
lemma dgCellModuleSourceEquivalence_hom :
    (dgCellModuleSourceEquivalence R D).hom =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleExtensionInfinity R (DGCategoryCellResolution.Source R D) D
        (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.augmentation R D) := rfl
/-- 元の一般 kernel の実作用を、同じ cell 増大と指定入力逆で比較する。 -/
def dgKernelDerivedInfinity_cellSourceIso (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R E D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D E P)
      ((dgCellModuleSourceEquivalence R D).inv ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R (DGCategoryCellResolution.Source R D) E
          ((_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.augmentation R D).comp P)) := by
  let e := dgCellModuleSourceEquivalence R D
  let K := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D E P
  have a := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_sourceRestrictionIso R
    (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R D) D E (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.augmentation R D) P
  have b := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp e.invHomIso K).symm
  have c := a.precomp e.inv
  simpa only [Category.assoc, Category.id_comp] using! (b ≪≫ c)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
