module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.KernelComparisons.DGKernelCellModel
public import SerrePositivity.DifferentialGraded.Bimodule.DiagonalRestriction
/-!
概要：cell 圏の対角双加群を元の対角の両端制限へ写す実増大。
方針：指定 dg 増大の全 Hom 鎖写像と準同型性を使う。
規約：原 Hom の平坦性は不要。使われ方：cell 模型の単位比較。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
local notation "DC" => DGCategoryCellResolution.Source R D
def dgKernelCellDiagonalAugmentation :
    BimoduleCategory.of R DC DC (Bimodule.diagonal R DC) ⟶
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellRestriction R D D (Bimodule.diagonal R D) :=
  Bimodule.diagonalRestrictionMap R DC D (DGCategoryCellResolution.augmentation R D)
lemma dgKernelCellDiagonalAugmentation_quasiIso :
    BimoduleCategory.quasiIso R DC DC (dgKernelCellDiagonalAugmentation R D) := by
  exact (Bimodule.diagonalRestrictionMap_quasiIso_iff R DC D
    (DGCategoryCellResolution.augmentation R D)).mpr
      (DGCategoryCellResolution.augmentation_homQuasiIso R D)
end
end SerrePositivity.InfinityCategories.Project.DerivedCategories
