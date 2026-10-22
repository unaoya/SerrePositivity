module
public import SerrePositivity.InfinityCategories.Derived.DGKernelCellCoherentComposition
public import SerrePositivity.InfinityCategories.Derived.DGKernelCellSourceUnitSpan
public import SerrePositivity.InfinityCategories.Derived.DGKernelCellTargetUnitSpan
public import SerrePositivity.InfinityCategories.Derived.FunctorIsoSandwichSourceUnitTransfer
public import SerrePositivity.InfinityCategories.Derived.FunctorIsoSandwichTargetUnitTransfer
/-!
概要：coherent cell 合成子の両単位三角式を実 diagonal tensor span で証明する。
方針：指定 canonical cell 単位の正方形と実 tensor span の κ 正方形を代入する。
規約：原 kernel の平坦性・旧比較の三角式を仮定しない。使われ方：一般合成 coherence。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded SSet
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] (D E : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E] (P : Bimodule R E D)
local notation "DC" => DGCategoryCellResolution.Source R D
local notation "EC" => DGCategoryCellResolution.Source R E
local notation "eD" => dgCellModuleSourceEquivalence R D
local notation "eE" => dgCellModuleSourceEquivalence R E
local notation "m" => BimoduleCategory.underlying R EC DC (dgKernelCellModel R D E P)
local notation "iD" => BimoduleCategory.underlying R DC DC
  (dgKernelCellModel R D D (Bimodule.diagonal R D))
local notation "iE" => BimoduleCategory.underlying R EC EC
  (dgKernelCellModel R E E (Bimodule.diagonal R E))
lemma dgKernelDerivedInfinity_compositionCellCoherentIso_source_unit :
    dgKernelDerivedInfinity_compositionCellCoherentIso R D D E (Bimodule.diagonal R D) P ≪≫
      ((dgKernelCellSourceUnitComparisonIso R D E P).postcomp (eE).hom).precomp (eD).inv ≪≫
      (dgKernelDerivedInfinity_cellModelIso R D E P).symm =
    (dgKernelDerivedInfinity_identityIso R D).postcomp (dgKernelDerivedInfinity R D E P) := by
  exact functorIsoSandwichCompositor_source_unit_transfer eD (eE).hom
    (dgKernelDerivedInfinity R D D (Bimodule.diagonal R D)) (dgKernelDerivedInfinity R D E P)
    (dgKernelDerivedInfinity R DC DC iD) (dgKernelDerivedInfinity R DC EC m)
    (dgKernelDerivedInfinity R DC EC
      (dgKernelCellComposite R D D E (Bimodule.diagonal R D) P))
    (dgKernelDerivedInfinity_cellModelIso R D D (Bimodule.diagonal R D))
    (dgKernelDerivedInfinity_cellModelIso R D E P)
    (dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R DC DC EC iD m
      (dgKernelCellModel_rightRelativeKFlat R D D (Bimodule.diagonal R D)))
    (dgKernelDerivedInfinity_identityIso R D) (dgKernelCellDiagonalUnitIso R D)
    (dgKernelCellSourceUnitComparisonIso R D E P) (dgKernelCellDiagonalUnitIso_value R D)
    (dgKernelCellSourceUnitComparisonIso_value R D E P)
lemma dgKernelDerivedInfinity_compositionCellCoherentIso_target_unit :
    dgKernelDerivedInfinity_compositionCellCoherentIso R D E E P (Bimodule.diagonal R E) ≪≫
      ((dgKernelCellTargetUnitComparisonIso R D E P).postcomp (eE).hom).precomp (eD).inv ≪≫
      (dgKernelDerivedInfinity_cellModelIso R D E P).symm =
    (dgKernelDerivedInfinity_identityIso R E).precomp (dgKernelDerivedInfinity R D E P) := by
  exact functorIsoSandwichCompositor_target_unit_transfer eE (eD).inv
    (dgKernelDerivedInfinity R D E P) (dgKernelDerivedInfinity R E E (Bimodule.diagonal R E))
    (dgKernelDerivedInfinity R DC EC m) (dgKernelDerivedInfinity R EC EC iE)
    (dgKernelDerivedInfinity R DC EC
      (dgKernelCellComposite R D E E P (Bimodule.diagonal R E)))
    (dgKernelDerivedInfinity_cellModelIso R D E P)
    (dgKernelDerivedInfinity_cellModelIso R E E (Bimodule.diagonal R E))
    (dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R DC EC EC m iE
      (dgKernelCellModel_rightRelativeKFlat R D E P))
    (dgKernelDerivedInfinity_identityIso R E) (dgKernelCellDiagonalUnitIso R E)
    (dgKernelCellTargetUnitComparisonIso R D E P) (dgKernelCellDiagonalUnitIso_value R E)
    (dgKernelCellTargetUnitComparisonIso_value R D E P)
end
end SerrePositivity.InfinityCategories
