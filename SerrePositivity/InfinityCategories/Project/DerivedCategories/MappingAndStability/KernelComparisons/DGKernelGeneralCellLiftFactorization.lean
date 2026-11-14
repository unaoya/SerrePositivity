module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.KernelComparisons.DGKernelGeneralCellLiftComposition
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.SimplicialFunctors.FunctorIsoSandwichCompositor
/-!
概要：一般 cell 模型の合成比較を元の三段合成として厳密に回収する。
方針：同じ全体比較の自然性と指定 K-flat 合成子の自然性を接続する。
規約：模型の augmentation 正方形は厳密。原 kernel の平坦性は不要。
使われ方：一般 cell 模型の変更と合成の coherence。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
variable (R : Type u) [CommRing R] (D E K : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R K] [Small.{u} K]
local notation "DC" => _root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R D
local notation "EC" => _root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R E
local notation "KC" => _root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R K
local notation "LD" => _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.middleLeftRestrictionFunctor R E D DC
  (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.augmentation R D)
local notation "RE" => _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.middleRightRestrictionFunctor R E EC DC
  (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.augmentation R E)
local notation "LE" => _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.middleLeftRestrictionFunctor R K E EC
  (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.augmentation R E)
local notation "RK" => _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.middleRightRestrictionFunctor R K KC EC
  (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.augmentation R K)
lemma dgKernelDerivedInfinity_compositionCellLiftIso_factorization
    (P : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E D) (Q : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R K E)
    (M : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R EC DC) (N : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R KC EC)
    (p : M ⟶ (RE).obj ((LD).obj P)) (q : N ⟶ (RK).obj ((LE).obj Q))
    (hM : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R EC DC (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R EC DC M))
    (hN : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R KC EC (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R KC EC N))
    (hp : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.quasiIso R EC DC p)
    (hq : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.quasiIso R KC EC q) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_compositionCellLiftIso R D E K P Q M N p q hM hN hp hq =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIsoSandwichCompositor
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R D).inv
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R E).hom
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R E).inv
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R K).hom
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R E).homInvIso
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D E (BimoduleCategory.underlying R E D P))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R E K (BimoduleCategory.underlying R K E Q))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R DC EC (BimoduleCategory.underlying R EC DC M))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R EC KC (BimoduleCategory.underlying R KC EC N))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R DC KC (BimoduleTensor.compose R KC EC DC
          (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R KC EC N) (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R EC DC M)))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_cellModelLiftIso R D E P M p hM hp)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_cellModelLiftIso R E K Q N q hN hq)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R DC EC KC
          (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R EC DC M)
          (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R KC EC N) hM) := rfl
end SerrePositivity.InfinityCategories.Project.DerivedCategories
