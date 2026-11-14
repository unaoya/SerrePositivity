module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.KernelComparisons.DGKernelTargetModelComparisonValue
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.KernelComparisons.DGKernelCellModelComparison
/-!
概要：指定済みの canonical cell 模型比較を、同じ増大上の別模型の比較へ接続する。
方針：元の出力比較の式を代入し、同じ cell 始域の指定逆で前合成する。
規約：元の比較・指定逆を変更しない。使われ方：一般 cell 模型の選択整合性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet DifferentialGraded MonoidalClosed
variable (R : Type u) [CommRing R] (D E : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
  (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R E D)
local notation "DC" => _root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R D
local notation "EC" => _root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R E
local notation "FE" => _root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.augmentation R E
local notation "Q0" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellModel R D E P
lemma dgKernelCellModel_targetIso_comparison
    (Q : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R EC DC)
    (q : Q ⟶ (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.middleRightRestrictionFunctor R E EC DC FE).obj
      (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.of R E DC ((_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.augmentation R D).comp P)))
    (b : Q0 ⟶ Q) (h : b ≫ q = ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellResolution R D E P).π))
    (hQ : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R EC DC (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R EC DC Q))
    (hq : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.quasiIso R EC DC q) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_mapIso_of_quasiIso R DC EC b
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTargetModel_map_quasiIso R DC EC E FE ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellResolution R D E P).π) q b h
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellResolution R D E P).quasiIso hq))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R E).hom =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellModel_targetIso R D E P ≪≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_targetModelIso R DC EC E FE (BimoduleCategory.of R E DC
          ((_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.augmentation R D).comp P)) Q q
          (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.augmentation_quasiEquivalence R E) hQ hq).symm := by
  have hh := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_targetModel_comparison_postcomp R DC EC E FE
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellResolution R D E P).π) q b h
      (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.augmentation_quasiEquivalence R E)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellModel_rightRelativeKFlat R D E P) hQ
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellResolution R D E P).quasiIso hq
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellModel_targetIso, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence_hom] using! hh
end SerrePositivity.InfinityCategories.Project.DerivedCategories
