module
public import SerrePositivity.InfinityCategories.Derived.DGKernelCellCompositionNaturality
public import SerrePositivity.InfinityCategories.Derived.DGKernelCellModelStrictLift
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
variable {P0 P1 : BimoduleCategory R E D} {Q0 Q1 : BimoduleCategory R K E}
local notation "P0u" => BimoduleCategory.underlying R E D P0
local notation "CP0" => dgKernelCellModel R D E P0u
local notation "RP0" => dgKernelCellResolution R D E P0u
local notation "Q0u" => BimoduleCategory.underlying R K E Q0
local notation "CQ0" => dgKernelCellModel R E K Q0u
local notation "RQ0" => dgKernelCellResolution R E K Q0u
local notation "F0" => dgKernelDerivedInfinity R D E P0u
local notation "G0" => dgKernelDerivedInfinity R E K Q0u
local notation "T0" => dgKernelDerivedInfinity R DC KC
  (dgKernelCellComposite R D E K P0u Q0u)
local notation "k0" => dgKernelDerivedInfinity_compositionCellIso R D E K P0u Q0u
local notation "P1u" => BimoduleCategory.underlying R E D P1
local notation "CP1" => dgKernelCellModel R D E P1u
local notation "RP1" => dgKernelCellResolution R D E P1u
local notation "Q1u" => BimoduleCategory.underlying R K E Q1
local notation "CQ1" => dgKernelCellModel R E K Q1u
local notation "RQ1" => dgKernelCellResolution R E K Q1u
local notation "F1" => dgKernelDerivedInfinity R D E P1u
local notation "G1" => dgKernelDerivedInfinity R E K Q1u
local notation "T1" => dgKernelDerivedInfinity R DC KC
  (dgKernelCellComposite R D E K P1u Q1u)
local notation "k1" => dgKernelDerivedInfinity_compositionCellIso R D E K P1u Q1u
lemma dgKernelDerivedInfinity_compositionCellIso_hom_naturality_strictLift
    (f : P0 ⟶ P1) (g : Q0 ⟶ Q1) :
    (k0).hom ≫ functorHomPrecomp
        (T0 ≫ (dgCellModuleSourceEquivalence R K).hom)
        (T1 ≫ (dgCellModuleSourceEquivalence R K).hom)
        (dgCellModuleSourceEquivalence R D).inv
        (functorHomPostcomp T0 T1 (dgCellModuleSourceEquivalence R K).hom
          ((dgKernelDerivedFunctorHomFunctor R DC KC).map
            (BimoduleTensor.composeMap R KC EC DC
              (dgKernelCellModelStrictLift R E K g) (dgKernelCellModelStrictLift R D E f)))) =
      (functorHomPostcomp F0 F1 G0 ((dgKernelDerivedFunctorHomFunctor R D E).map f) ≫
        functorHomPrecomp G0 G1 F1 ((dgKernelDerivedFunctorHomFunctor R E K).map g)) ≫
        (k1).hom := by
  exact dgKernelDerivedInfinity_compositionCellIso_hom_naturality R D E K f g
    (dgKernelCellModelStrictLift R D E f) (dgKernelCellModelStrictLift R E K g)
    (dgKernelCellModelStrictLift_fac R D E f) (dgKernelCellModelStrictLift_fac R E K g)
end SerrePositivity.InfinityCategories
