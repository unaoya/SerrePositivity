module
public import SerrePositivity.InfinityCategories.Derived.DGKernelGeneralComposition
public import SerrePositivity.InfinityCategories.Derived.FunctorIsoSandwichPentagon
/-!
概要：元の指定 cell 合成比較を一般合成子の同じ値として回収する。
方針：指定された比較値と平坦模型の既存五角式を、始域同値から反映する。
規約：原 kernel の平坦性・三角式は仮定しない。使われ方：一般 cell の coherence。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] (D E K : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
  [DGCategory R K] [Small.{u} K] (P : Bimodule R E D) (Q : Bimodule R K E)
local notation "DC" => DGCategoryCellResolution.Source R D
local notation "EC" => DGCategoryCellResolution.Source R E
local notation "KC" => DGCategoryCellResolution.Source R K
local notation "MP" => BimoduleCategory.underlying R EC DC (dgKernelCellModel R D E P)
local notation "MQ" => BimoduleCategory.underlying R KC EC (dgKernelCellModel R E K Q)
lemma dgKernelDerivedInfinity_compositionCellIso_sandwich :
    dgKernelDerivedInfinity_compositionCellIso R D E K P Q =
      functorIsoSandwichCompositor
        (dgCellModuleSourceEquivalence R D).inv
        (dgCellModuleSourceEquivalence R E).hom
        (dgCellModuleSourceEquivalence R E).inv
        (dgCellModuleSourceEquivalence R K).hom
        (dgCellModuleSourceEquivalence R E).homInvIso
        (dgKernelDerivedInfinity R D E P) (dgKernelDerivedInfinity R E K Q)
        (dgKernelDerivedInfinity R DC EC MP) (dgKernelDerivedInfinity R EC KC MQ)
        (dgKernelDerivedInfinity R DC KC (dgKernelCellComposite R D E K P Q))
        (dgKernelDerivedInfinity_cellModelIso R D E P)
        (dgKernelDerivedInfinity_cellModelIso R E K Q)
        (dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R DC EC KC MP MQ
          (dgKernelCellModel_rightRelativeKFlat R D E P)) := rfl
end
end SerrePositivity.InfinityCategories
