module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelCellDiagonalAugmentation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGBimoduleCanonicalStrictLift
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelCellLiftComparison
/-!
概要：cell diagonal の半自由分解から二つの実 diagonal 模型への span を構成する。
方針：元の増大に沿う厳密な canonical 持ち上げと準同型の二射合成を使う。
規約：原 Hom の平坦性は不要。使われ方：canonical cell 模型の単位比較。
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
def dgKernelCellDiagonalResolution : BimoduleSemifreeResolution R DC DC Δ :=
  _root_.SerrePositivity.DifferentialGraded.bimoduleCanonicalSemifreeResolution R DC DC Δ
def dgKernelCellDiagonalResolutionAugmentation :
    (dgKernelCellDiagonalResolution R D).obj ⟶
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellRestriction R D D (Bimodule.diagonal R D) :=
  (dgKernelCellDiagonalResolution R D).π ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellDiagonalAugmentation R D
lemma dgKernelCellDiagonalResolutionAugmentation_quasiIso :
    _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.quasiIso R DC DC (dgKernelCellDiagonalResolutionAugmentation R D) :=
  (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.quasiIso R DC DC).comp_mem _ _
    (dgKernelCellDiagonalResolution R D).quasiIso
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellDiagonalAugmentation_quasiIso R D)
def dgKernelCellDiagonalResolutionToCanonical :
    (dgKernelCellDiagonalResolution R D).obj ⟶ Q0 :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleCanonicalResolutionStrictLift R DC DC (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellDiagonalAugmentation R D)
lemma dgKernelCellDiagonalResolutionToCanonical_fac :
    dgKernelCellDiagonalResolutionToCanonical R D ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellResolution R D D (Bimodule.diagonal R D)).π =
        dgKernelCellDiagonalResolutionAugmentation R D :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleCanonicalResolutionStrictLift_fac R DC DC
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellDiagonalAugmentation R D)
lemma dgKernelCellDiagonalResolutionToCanonical_quasiIso :
    _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.quasiIso R DC DC (dgKernelCellDiagonalResolutionToCanonical R D) := by
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTargetModel_map_quasiIso R DC DC D
    (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.augmentation R D)
    (dgKernelCellDiagonalResolutionAugmentation R D)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellResolution R D D (Bimodule.diagonal R D)).π
    (dgKernelCellDiagonalResolutionToCanonical R D)
    (dgKernelCellDiagonalResolutionToCanonical_fac R D)
    (dgKernelCellDiagonalResolutionAugmentation_quasiIso R D)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellResolution R D D (Bimodule.diagonal R D)).quasiIso
end
end SerrePositivity.InfinityCategories.Project.DerivedCategories
