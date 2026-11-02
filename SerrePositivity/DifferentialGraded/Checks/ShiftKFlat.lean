module
public import SerrePositivity.DifferentialGraded.Tensor.Bimodule.KFlatness
public import SerrePositivity.DifferentialGraded.Category.Examples
public import Mathlib.Data.ZMod.Basic

/-! # 全整数shift比較と相対K-flat閉性の検査 -/
@[expose] public section
noncomputable section
universe u v
open CategoryTheory CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

example (F : DGFunctor A (RightModule A D) (Complex A)) (M : RightModule A D) (s : ℤ) :
    F.obj (shiftModule s M) ≅ (F.obj M)⟦s⟧ :=
  DGFunctor.moduleShiftImageIso A D F s M

example (M : RightModule A D) (L : LeftModule A D) :
    BalancedTensor.obj A D (shiftModule (-1) M) L ≅ (BalancedTensor.obj A D M L)⟦(-1 : ℤ)⟧ :=
  BalancedTensor.rightTensorShiftIso A D L (-1) M

example {M : ModuleCategory A D}
    (h : moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) M)) (s : ℤ) :
    moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) (M⟦s⟧)) :=
  moduleRelativeKFlat_shiftObj A D h s

example (M : RightModule A D) :
    compose A (moduleShiftInElement A D 0 M) (moduleShiftOutElement A D 0 M)
      (add_neg_cancel 0) = (unitElement A (shiftModule 0 M)).val :=
  moduleShiftOutIn A D 0 M

example (M : RightModule (ZMod 2) PUnit.{1}) (L : LeftModule (ZMod 2) PUnit.{1}) :
    BalancedTensor.obj (ZMod 2) PUnit.{1} (shiftModule 1 M) L ≅
      (BalancedTensor.obj (ZMod 2) PUnit.{1} M L)⟦(1 : ℤ)⟧ :=
  BalancedTensor.rightTensorShiftIso (ZMod 2) PUnit.{1} L 1 M

#print axioms homogeneous_XIsoOfEq_inv_comp
#print axioms moduleShiftOutElement
#print axioms moduleShiftOutElement_π
#print axioms moduleShiftOutElement_d
#print axioms moduleShiftIn_naturality
#print axioms moduleShiftInElement
#print axioms moduleShiftInElement_π
#print axioms moduleShiftOutIn
#print axioms moduleShiftInOut
#print axioms DGFunctor.moduleShiftImageOut
#print axioms DGFunctor.moduleShiftImageIn
#print axioms DGFunctor.moduleShiftImageOut_d
#print axioms DGFunctor.moduleShiftImageOutIn
#print axioms DGFunctor.moduleShiftImageInOut
#print axioms DGFunctor.moduleShiftImageComparison
#print axioms DGFunctor.moduleShiftImageComparison_f
#print axioms DGFunctor.moduleShiftImageComparison_bijective
#print axioms DGFunctor.moduleShiftImageComparison_isIso
#print axioms DGFunctor.moduleShiftImageIso
#print axioms BalancedTensor.rightTensorShiftIso
#print axioms moduleRelativeKFlat_shift
#print axioms moduleRelativeKFlat_shiftObj
