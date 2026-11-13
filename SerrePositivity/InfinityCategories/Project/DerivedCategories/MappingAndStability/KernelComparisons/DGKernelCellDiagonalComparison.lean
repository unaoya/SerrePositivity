module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.KernelComparisons.DGKernelCellDiagonalResolution
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.SpanPresentations.FunctorIsoWhiskerSpan
/-!
概要：canonical diagonal cell 模型と実 diagonal の比較を実 span の作用から構成する。
方針：共通の半自由始点、全 Hom 準同型と指定模型比較の自然性を使う。
規約：比較の値を保持する。使われ方：元の cell 単位の整合性。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
local notation "DC" => _root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R D
local notation "Δ" => _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.of R DC DC (_root_.SerrePositivity.DifferentialGraded.Bimodule.diagonal R DC)
local notation "P" => _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.of R D D (_root_.SerrePositivity.DifferentialGraded.Bimodule.diagonal R D)
local notation "Q0" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellModel R D D (Bimodule.diagonal R D)
local notation "ρ" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellDiagonalResolution R D
local notation "e" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R D
lemma dgKernelCellDiagonalResolution_rightRelativeKFlat :
    _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R DC DC (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R DC DC (ρ).obj) :=
  (ρ).rightRelativeKFlat R DC DC (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.source_homKFlat R D)
def dgKernelCellDiagonalLiftIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D D (Bimodule.diagonal R D))
      ((e).inv ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R DC DC (Bimodule.diagonal R DC) ≫ (e).hom) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_cellModelLiftIso R D D P Δ
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellDiagonalAugmentation R D) (Bimodule.diagonal_rightRelativeKFlat R DC)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellDiagonalAugmentation_quasiIso R D)
def dgKernelCellDiagonalComparisonIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R DC DC (BimoduleCategory.underlying R DC DC Q0))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R DC DC (Bimodule.diagonal R DC)) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_mapIso_of_quasiIso R DC DC
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellDiagonalResolutionToCanonical R D)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellDiagonalResolutionToCanonical_quasiIso R D)).symm ≪≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_mapIso_of_quasiIso R DC DC (ρ).π (ρ).quasiIso
lemma dgKernelCellDiagonalComparisonIso_value :
    ((dgKernelCellDiagonalComparisonIso R D).postcomp (e).hom).precomp (e).inv =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_cellModelIso R D D (Bimodule.diagonal R D)).symm ≪≫
        dgKernelCellDiagonalLiftIso R D := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_whisker_span_value
    (e).inv (e).hom
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R DC DC (BimoduleCategory.underlying R DC DC Q0))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R DC DC (Bimodule.diagonal R DC))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R DC DC (BimoduleCategory.underlying R DC DC (ρ).obj))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D D (Bimodule.diagonal R D))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_mapIso_of_quasiIso R DC DC
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellDiagonalResolutionToCanonical R D)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellDiagonalResolutionToCanonical_quasiIso R D))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_mapIso_of_quasiIso R DC DC (ρ).π (ρ).quasiIso)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_cellModelIso R D D (Bimodule.diagonal R D))
    (dgKernelCellDiagonalLiftIso R D)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_cellModelLiftIso R D D P (ρ).obj
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellDiagonalResolutionAugmentation R D)
      (dgKernelCellDiagonalResolution_rightRelativeKFlat R D)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellDiagonalResolutionAugmentation_quasiIso R D))
  · exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_cellModelLift_comparison_value R D D P
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellDiagonalResolutionAugmentation R D)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellResolution R D D (Bimodule.diagonal R D)).π
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellDiagonalResolutionToCanonical R D)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellDiagonalResolutionToCanonical_fac R D)
      (dgKernelCellDiagonalResolution_rightRelativeKFlat R D)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellModel_rightRelativeKFlat R D D (Bimodule.diagonal R D))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellDiagonalResolutionAugmentation_quasiIso R D)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellResolution R D D (Bimodule.diagonal R D)).quasiIso
  · exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_cellModelLift_comparison_value R D D P
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellDiagonalResolutionAugmentation R D)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellDiagonalAugmentation R D) (ρ).π rfl
      (dgKernelCellDiagonalResolution_rightRelativeKFlat R D)
      (_root_.SerrePositivity.DifferentialGraded.Bimodule.diagonal_rightRelativeKFlat R DC)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellDiagonalResolutionAugmentation_quasiIso R D)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellDiagonalAugmentation_quasiIso R D)
end
end SerrePositivity.InfinityCategories.Project.DerivedCategories
