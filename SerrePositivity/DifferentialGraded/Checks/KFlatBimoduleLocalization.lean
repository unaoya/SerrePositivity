module
public import SerrePositivity.DifferentialGraded.Derived.KFlatBimoduleResolution
public import Mathlib.Data.ZMod.Basic

/-! # K-flat因子間の準同型比較と因子局所化の受入監査 -/
@[expose] public section
noncomputable section
universe u v w z
open CategoryTheory
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.BimoduleTensor
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [Small.{u} B] [Small.{u} C]

example (N : LeftModuleCategory A C) :
    ∃ (L : LeftModuleCategory A C) (q : L ⟶ N),
      leftModuleRelativeKFlat A C (ForgetEnrichment.to (Complex A) L) ∧
        leftModuleQuasiIso A C q := exists_leftRelativeKFlat_resolution A C N

example (L : LeftModule A C) {M N : ModuleCategory A C}
    (hM : moduleRelativeKFlat A C (ForgetEnrichment.to (Complex A) M))
    (hN : moduleRelativeKFlat A C (ForgetEnrichment.to (Complex A) N))
    (f : M ⟶ N) (hf : moduleQuasiIso A C f) :
    QuasiIso ((BalancedTensor.rightTensorFunctor A C L).map f) :=
  BalancedTensor.rightTensor_relativeKFlat_quasiIso A C L hM hN f hf

example {Q Q' : BimoduleCategory A C E}
    (hQ : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q))
    (hQ' : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q'))
    (g : Q ⟶ Q') (hg : BimoduleCategory.quasiIso A C E g) :
    derivedComposeWith A B C E Q hQ ≅ derivedComposeWith A B C E Q' hQ' :=
  derivedComposeWithKFlatIso A B C E hQ hQ' g hg

example : rightKFlatToDerived A C E ⋙ rightFactorLocalizedComposeFunctor A B C E =
    derivedComposeWithFunctor A B C E := rightFactorLocalizedComposeFunctor_fac A B C E

example [Small.{u} E] (hE : localHomKFlat A E) :
    (rightKFlatDerivedInclusion A C E).EssSurj :=
  rightKFlatDerivedInclusion_essSurj A C E hE

example (C : Type w) (E : Type z) [DGCategory (ZMod 2) C] [DGCategory (ZMod 2) E]
    [Small.{0} C] [Small.{0} E] (hE : localHomKFlat (ZMod 2) E) :
    (rightKFlatDerivedInclusion (ZMod 2) C E).EssSurj :=
  rightKFlatDerivedInclusion_essSurj (ZMod 2) C E hE

#print axioms leftRightOpposite_inverse_quasiIso_iff
#print axioms leftModuleRelativeKFlat
#print axioms leftModuleRelativeKFlat_preserves_rightQuasiIso
#print axioms exists_leftRelativeKFlat_resolution
#print axioms BalancedTensor.rightTensor_relativeKFlat_quasiIso
#print axioms composeMap_second_kFlat_quasiIso
#print axioms composeMap_kFlat_quasiIso
#print axioms composeWithKFlatIso
#print axioms composeWithKFlatIso_hom
#print axioms derivedComposeWithKFlatIso
#print axioms derivedComposeWithKFlatIso_hom
#print axioms derivedComposeWithKFlatIso_id
#print axioms derivedComposeWithKFlatIso_trans
#print axioms rightKFlatInclusion
#print axioms rightKFlatQuasiIso
#print axioms DerivedRightKFlatBimoduleCategory
#print axioms rightKFlatToDerived
#print axioms rightKFlatDerivedInclusion
#print axioms rightKFlatDerivedInclusion_fac
#print axioms derivedComposeWithFunctor_inverts
#print axioms rightFactorLocalizedComposeFunctor
#print axioms rightFactorLocalizedComposeFunctor_fac
#print axioms rightFactorLocalizedComposeFunctor_map_base
#print axioms rightKFlatResolutionObj
#print axioms rightKFlatResolutionDerivedIso
#print axioms rightKFlatDerivedInclusion_essSurj
