module
public import SerrePositivity.InfinityCategories.Derived.DGKernelGeneralCellLiftComposition
public import SerrePositivity.InfinityCategories.Derived.FunctorIsoSandwichCompositor
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
variable (R : Type u) [CommRing R] (D E K : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
  [DGCategory R K] [Small.{u} K]
local notation "DC" => DGCategoryCellResolution.Source R D
local notation "EC" => DGCategoryCellResolution.Source R E
local notation "KC" => DGCategoryCellResolution.Source R K
local notation "LD" => BimoduleCategory.middleLeftRestrictionFunctor R E D DC
  (DGCategoryCellResolution.augmentation R D)
local notation "RE" => BimoduleCategory.middleRightRestrictionFunctor R E EC DC
  (DGCategoryCellResolution.augmentation R E)
local notation "LE" => BimoduleCategory.middleLeftRestrictionFunctor R K E EC
  (DGCategoryCellResolution.augmentation R E)
local notation "RK" => BimoduleCategory.middleRightRestrictionFunctor R K KC EC
  (DGCategoryCellResolution.augmentation R K)
lemma dgKernelDerivedInfinity_compositionCellLiftIso_factorization
    (P : BimoduleCategory R E D) (Q : BimoduleCategory R K E)
    (M : BimoduleCategory R EC DC) (N : BimoduleCategory R KC EC)
    (p : M ⟶ (RE).obj ((LD).obj P)) (q : N ⟶ (RK).obj ((LE).obj Q))
    (hM : Bimodule.rightRelativeKFlat R EC DC (BimoduleCategory.underlying R EC DC M))
    (hN : Bimodule.rightRelativeKFlat R KC EC (BimoduleCategory.underlying R KC EC N))
    (hp : BimoduleCategory.quasiIso R EC DC p)
    (hq : BimoduleCategory.quasiIso R KC EC q) :
    dgKernelDerivedInfinity_compositionCellLiftIso R D E K P Q M N p q hM hN hp hq =
      functorIsoSandwichCompositor
        (dgCellModuleSourceEquivalence R D).inv
        (dgCellModuleSourceEquivalence R E).hom
        (dgCellModuleSourceEquivalence R E).inv
        (dgCellModuleSourceEquivalence R K).hom
        (dgCellModuleSourceEquivalence R E).homInvIso
        (dgKernelDerivedInfinity R D E (BimoduleCategory.underlying R E D P))
        (dgKernelDerivedInfinity R E K (BimoduleCategory.underlying R K E Q))
        (dgKernelDerivedInfinity R DC EC (BimoduleCategory.underlying R EC DC M))
        (dgKernelDerivedInfinity R EC KC (BimoduleCategory.underlying R KC EC N))
        (dgKernelDerivedInfinity R DC KC (BimoduleTensor.compose R KC EC DC
          (BimoduleCategory.underlying R KC EC N) (BimoduleCategory.underlying R EC DC M)))
        (dgKernelDerivedInfinity_cellModelLiftIso R D E P M p hM hp)
        (dgKernelDerivedInfinity_cellModelLiftIso R E K Q N q hN hq)
        (dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R DC EC KC
          (BimoduleCategory.underlying R EC DC M)
          (BimoduleCategory.underlying R KC EC N) hM) := rfl
end SerrePositivity.InfinityCategories
