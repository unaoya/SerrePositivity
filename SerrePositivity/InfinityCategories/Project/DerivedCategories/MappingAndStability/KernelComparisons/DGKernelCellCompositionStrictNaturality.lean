module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.KernelComparisons.DGKernelCellCompositionNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.KernelComparisons.DGKernelCellModelStrictLift
/-!
概要：任意の二つの元 kernel 射に対する元の cell 合成比較の実自然性を証明する。
方針：構成済みの指定 strict lift とその厳密な augmentation square を代入する。
規約：追加の模型射・持ち上げ仮定は不要。使われ方：一般合成の coherence。
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
variable {P0 P1 : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E D} {Q0 Q1 : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R K E}
local notation "P0u" => _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D P0
local notation "CP0" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellModel R D E P0u
local notation "RP0" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellResolution R D E P0u
local notation "Q0u" => _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R K E Q0
local notation "CQ0" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellModel R E K Q0u
local notation "RQ0" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellResolution R E K Q0u
local notation "F0" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D E P0u
local notation "G0" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R E K Q0u
local notation "T0" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R DC KC
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellComposite R D E K P0u Q0u)
local notation "k0" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_compositionCellIso R D E K P0u Q0u
local notation "P1u" => _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D P1
local notation "CP1" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellModel R D E P1u
local notation "RP1" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellResolution R D E P1u
local notation "Q1u" => _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R K E Q1
local notation "CQ1" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellModel R E K Q1u
local notation "RQ1" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellResolution R E K Q1u
local notation "F1" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D E P1u
local notation "G1" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R E K Q1u
local notation "T1" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R DC KC
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellComposite R D E K P1u Q1u)
local notation "k1" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_compositionCellIso R D E K P1u Q1u
lemma dgKernelDerivedInfinity_compositionCellIso_hom_naturality_strictLift
    (f : P0 ⟶ P1) (g : Q0 ⟶ Q1) :
    (k0).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp
        (T0 ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R K).hom)
        (T1 ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R K).hom)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R D).inv
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp T0 T1 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R K).hom
          ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor R DC KC).map
            (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.composeMap R KC EC DC
              (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellModelStrictLift R E K g) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellModelStrictLift R D E f)))) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp F0 F1 G0 ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor R D E).map f) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp G0 G1 F1 ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor R E K).map g)) ≫
        (k1).hom := by
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_compositionCellIso_hom_naturality R D E K f g
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellModelStrictLift R D E f) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellModelStrictLift R E K g)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellModelStrictLift_fac R D E f) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellModelStrictLift_fac R E K g)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
