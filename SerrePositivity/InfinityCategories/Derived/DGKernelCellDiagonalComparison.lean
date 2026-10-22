module
public import SerrePositivity.InfinityCategories.Derived.DGKernelCellDiagonalResolution
public import SerrePositivity.InfinityCategories.Derived.FunctorIsoWhiskerSpan
/-!
概要：canonical diagonal cell 模型と実 diagonal の比較を実 span の作用から構成する。
方針：共通の半自由始点、全 Hom 準同型と指定模型比較の自然性を使う。
規約：比較の値を保持する。使われ方：元の cell 単位の整合性。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
local notation "DC" => DGCategoryCellResolution.Source R D
local notation "Δ" => BimoduleCategory.of R DC DC (Bimodule.diagonal R DC)
local notation "P" => BimoduleCategory.of R D D (Bimodule.diagonal R D)
local notation "Q0" => dgKernelCellModel R D D (Bimodule.diagonal R D)
local notation "ρ" => dgKernelCellDiagonalResolution R D
local notation "e" => dgCellModuleSourceEquivalence R D
lemma dgKernelCellDiagonalResolution_rightRelativeKFlat :
    Bimodule.rightRelativeKFlat R DC DC (BimoduleCategory.underlying R DC DC (ρ).obj) :=
  (ρ).rightRelativeKFlat R DC DC (DGCategoryCellResolution.source_homKFlat R D)
def dgKernelCellDiagonalLiftIso :
    FunctorIso (dgKernelDerivedInfinity R D D (Bimodule.diagonal R D))
      ((e).inv ≫ dgKernelDerivedInfinity R DC DC (Bimodule.diagonal R DC) ≫ (e).hom) :=
  dgKernelDerivedInfinity_cellModelLiftIso R D D P Δ
    (dgKernelCellDiagonalAugmentation R D) (Bimodule.diagonal_rightRelativeKFlat R DC)
    (dgKernelCellDiagonalAugmentation_quasiIso R D)
def dgKernelCellDiagonalComparisonIso :
    FunctorIso
      (dgKernelDerivedInfinity R DC DC (BimoduleCategory.underlying R DC DC Q0))
      (dgKernelDerivedInfinity R DC DC (Bimodule.diagonal R DC)) :=
  (dgKernelDerivedInfinity_mapIso_of_quasiIso R DC DC
    (dgKernelCellDiagonalResolutionToCanonical R D)
    (dgKernelCellDiagonalResolutionToCanonical_quasiIso R D)).symm ≪≫
      dgKernelDerivedInfinity_mapIso_of_quasiIso R DC DC (ρ).π (ρ).quasiIso
lemma dgKernelCellDiagonalComparisonIso_value :
    ((dgKernelCellDiagonalComparisonIso R D).postcomp (e).hom).precomp (e).inv =
      (dgKernelDerivedInfinity_cellModelIso R D D (Bimodule.diagonal R D)).symm ≪≫
        dgKernelCellDiagonalLiftIso R D := by
  apply functorIso_whisker_span_value
    (e).inv (e).hom
    (dgKernelDerivedInfinity R DC DC (BimoduleCategory.underlying R DC DC Q0))
    (dgKernelDerivedInfinity R DC DC (Bimodule.diagonal R DC))
    (dgKernelDerivedInfinity R DC DC (BimoduleCategory.underlying R DC DC (ρ).obj))
    (dgKernelDerivedInfinity R D D (Bimodule.diagonal R D))
    (dgKernelDerivedInfinity_mapIso_of_quasiIso R DC DC
      (dgKernelCellDiagonalResolutionToCanonical R D)
      (dgKernelCellDiagonalResolutionToCanonical_quasiIso R D))
    (dgKernelDerivedInfinity_mapIso_of_quasiIso R DC DC (ρ).π (ρ).quasiIso)
    (dgKernelDerivedInfinity_cellModelIso R D D (Bimodule.diagonal R D))
    (dgKernelCellDiagonalLiftIso R D)
    (dgKernelDerivedInfinity_cellModelLiftIso R D D P (ρ).obj
      (dgKernelCellDiagonalResolutionAugmentation R D)
      (dgKernelCellDiagonalResolution_rightRelativeKFlat R D)
      (dgKernelCellDiagonalResolutionAugmentation_quasiIso R D))
  · exact dgKernelDerivedInfinity_cellModelLift_comparison_value R D D P
      (dgKernelCellDiagonalResolutionAugmentation R D)
      (dgKernelCellResolution R D D (Bimodule.diagonal R D)).π
      (dgKernelCellDiagonalResolutionToCanonical R D)
      (dgKernelCellDiagonalResolutionToCanonical_fac R D)
      (dgKernelCellDiagonalResolution_rightRelativeKFlat R D)
      (dgKernelCellModel_rightRelativeKFlat R D D (Bimodule.diagonal R D))
      (dgKernelCellDiagonalResolutionAugmentation_quasiIso R D)
      (dgKernelCellResolution R D D (Bimodule.diagonal R D)).quasiIso
  · exact dgKernelDerivedInfinity_cellModelLift_comparison_value R D D P
      (dgKernelCellDiagonalResolutionAugmentation R D)
      (dgKernelCellDiagonalAugmentation R D) (ρ).π rfl
      (dgKernelCellDiagonalResolution_rightRelativeKFlat R D)
      (Bimodule.diagonal_rightRelativeKFlat R DC)
      (dgKernelCellDiagonalResolutionAugmentation_quasiIso R D)
      (dgKernelCellDiagonalAugmentation_quasiIso R D)
end
end SerrePositivity.InfinityCategories
