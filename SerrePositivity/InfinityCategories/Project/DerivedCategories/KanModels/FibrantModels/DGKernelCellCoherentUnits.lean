module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.FibrantModels.DGKernelCellCoherentComposition
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.SpanPresentations.DGKernelCellSourceUnitSpan
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.SpanPresentations.DGKernelCellTargetUnitSpan
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.SimplicialFunctors.FunctorIsoSandwichSourceUnitTransfer
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.SimplicialFunctors.FunctorIsoSandwichTargetUnitTransfer
/-!
概要：coherent cell 合成子の両単位三角式を実 diagonal tensor span で証明する。
方針：指定 canonical cell 単位の正方形と実 tensor span の κ 正方形を代入する。
規約：原 kernel の平坦性・旧比較の三角式を仮定しない。使われ方：一般合成 coherence。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] (D E : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E] (P : Bimodule R E D)
local notation "DC" => DGCategoryCellResolution.Source R D
local notation "EC" => DGCategoryCellResolution.Source R E
local notation "eD" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R D
local notation "eE" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R E
local notation "m" => BimoduleCategory.underlying R EC DC (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellModel R D E P)
local notation "iD" => BimoduleCategory.underlying R DC DC
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellModel R D D (Bimodule.diagonal R D))
local notation "iE" => BimoduleCategory.underlying R EC EC
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellModel R E E (Bimodule.diagonal R E))
lemma dgKernelDerivedInfinity_compositionCellCoherentIso_source_unit :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_compositionCellCoherentIso R D D E (Bimodule.diagonal R D) P ≪≫
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellSourceUnitComparisonIso R D E P).postcomp (eE).hom).precomp (eD).inv ≪≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_cellModelIso R D E P).symm =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_identityIso R D).postcomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D E P) := by
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIsoSandwichCompositor_source_unit_transfer eD (eE).hom
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D D (Bimodule.diagonal R D)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D E P)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R DC DC iD) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R DC EC m)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R DC EC
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellComposite R D D E (Bimodule.diagonal R D) P))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_cellModelIso R D D (Bimodule.diagonal R D))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_cellModelIso R D E P)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R DC DC EC iD m
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellModel_rightRelativeKFlat R D D (Bimodule.diagonal R D)))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_identityIso R D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellDiagonalUnitIso R D)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellSourceUnitComparisonIso R D E P) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellDiagonalUnitIso_value R D)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellSourceUnitComparisonIso_value R D E P)
lemma dgKernelDerivedInfinity_compositionCellCoherentIso_target_unit :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_compositionCellCoherentIso R D E E P (Bimodule.diagonal R E) ≪≫
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellTargetUnitComparisonIso R D E P).postcomp (eE).hom).precomp (eD).inv ≪≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_cellModelIso R D E P).symm =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_identityIso R E).precomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D E P) := by
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIsoSandwichCompositor_target_unit_transfer eE (eD).inv
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D E P) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R E E (Bimodule.diagonal R E))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R DC EC m) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R EC EC iE)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R DC EC
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellComposite R D E E P (Bimodule.diagonal R E)))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_cellModelIso R D E P)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_cellModelIso R E E (Bimodule.diagonal R E))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R DC EC EC m iE
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellModel_rightRelativeKFlat R D E P))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_identityIso R E) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellDiagonalUnitIso R E)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellTargetUnitComparisonIso R D E P) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellDiagonalUnitIso_value R E)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellTargetUnitComparisonIso_value R D E P)
end
end SerrePositivity.InfinityCategories.Project.DerivedCategories
