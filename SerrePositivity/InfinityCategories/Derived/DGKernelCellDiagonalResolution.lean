module
public import SerrePositivity.InfinityCategories.Derived.DGKernelCellDiagonalAugmentation
public import SerrePositivity.InfinityCategories.Derived.DGBimoduleCanonicalStrictLift
public import SerrePositivity.InfinityCategories.Derived.DGKernelCellLiftComparison
/-!
概要：cell diagonal の半自由分解から二つの実 diagonal 模型への span を構成する。
方針：元の増大に沿う厳密な canonical 持ち上げと準同型の二射合成を使う。
規約：原 Hom の平坦性は不要。使われ方：canonical cell 模型の単位比較。
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
def dgKernelCellDiagonalResolution : BimoduleSemifreeResolution R DC DC Δ :=
  bimoduleCanonicalSemifreeResolution R DC DC Δ
def dgKernelCellDiagonalResolutionAugmentation :
    (dgKernelCellDiagonalResolution R D).obj ⟶
      dgKernelCellRestriction R D D (Bimodule.diagonal R D) :=
  (dgKernelCellDiagonalResolution R D).π ≫ dgKernelCellDiagonalAugmentation R D
lemma dgKernelCellDiagonalResolutionAugmentation_quasiIso :
    BimoduleCategory.quasiIso R DC DC (dgKernelCellDiagonalResolutionAugmentation R D) :=
  (BimoduleCategory.quasiIso R DC DC).comp_mem _ _
    (dgKernelCellDiagonalResolution R D).quasiIso
    (dgKernelCellDiagonalAugmentation_quasiIso R D)
def dgKernelCellDiagonalResolutionToCanonical :
    (dgKernelCellDiagonalResolution R D).obj ⟶ Q0 :=
  dgBimoduleCanonicalResolutionStrictLift R DC DC (dgKernelCellDiagonalAugmentation R D)
lemma dgKernelCellDiagonalResolutionToCanonical_fac :
    dgKernelCellDiagonalResolutionToCanonical R D ≫
      (dgKernelCellResolution R D D (Bimodule.diagonal R D)).π =
        dgKernelCellDiagonalResolutionAugmentation R D :=
  dgBimoduleCanonicalResolutionStrictLift_fac R DC DC
    (dgKernelCellDiagonalAugmentation R D)
lemma dgKernelCellDiagonalResolutionToCanonical_quasiIso :
    BimoduleCategory.quasiIso R DC DC (dgKernelCellDiagonalResolutionToCanonical R D) := by
  exact dgKernelTargetModel_map_quasiIso R DC DC D
    (DGCategoryCellResolution.augmentation R D)
    (dgKernelCellDiagonalResolutionAugmentation R D)
    (dgKernelCellResolution R D D (Bimodule.diagonal R D)).π
    (dgKernelCellDiagonalResolutionToCanonical R D)
    (dgKernelCellDiagonalResolutionToCanonical_fac R D)
    (dgKernelCellDiagonalResolutionAugmentation_quasiIso R D)
    (dgKernelCellResolution R D D (Bimodule.diagonal R D)).quasiIso
end
end SerrePositivity.InfinityCategories
