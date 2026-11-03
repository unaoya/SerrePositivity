module
public import SerrePositivity.DifferentialGraded.Functor.ModuleShift
public import SerrePositivity.DifferentialGraded.Tensor.Enriched
public import SerrePositivity.DifferentialGraded.Tensor.Bimodule.KFlatness
public import SerrePositivity.DifferentialGraded.Category.Basic
public import Mathlib.Data.ZMod.Basic

/-! # 任意複体値dg関手の標準cone保存 -/
@[expose] public section
noncomputable section
universe u v
open CategoryTheory CochainComplex
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.DGFunctor
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

example (F : DGFunctor A (RightModule A D) (Complex A)) {M N : ModuleCategory A D} (f : M ⟶ N) :
    mappingCone ((F.toComplexFunctor A).map f) ≅ (F.toComplexFunctor A).obj (moduleCone A D f) :=
  moduleConeImageIso A D F f

example (L : LeftModule A D) {M N : ModuleCategory A D} (f : M ⟶ N) :
    IsIso (moduleConeImageComparison A D (BalancedTensor.rightTensorDG A D L) f) :=
  moduleConeImageComparison_isIso A D _ f

example {M N : ModuleCategory A D} (f : M ⟶ N)
    (hM : moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) M))
    (hN : moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) N)) :
    moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) (moduleCone A D f)) :=
  moduleRelativeKFlat_cone A D f hM hN

example {M N : ModuleCategory A D} (f : M ⟶ N) (x : D) :
    (moduleConeImageIso A D (moduleEvaluationDG A D x) f).hom =
      moduleConeImageComparison A D (moduleEvaluationDG A D x) f :=
  moduleConeImageIso_hom A D _ f

example {M N : ModuleCategory (ZMod 2) PUnit.{1}} (f : M ⟶ N) (x : PUnit.{1}) :
    mappingCone (((moduleEvaluationDG (ZMod 2) PUnit.{1} x).toComplexFunctor (ZMod 2)).map f) ≅
      ((moduleEvaluationDG (ZMod 2) PUnit.{1} x).toComplexFunctor (ZMod 2)).obj
        (moduleCone (ZMod 2) PUnit.{1} f) :=
  moduleConeImageIso (ZMod 2) PUnit.{1} (moduleEvaluationDG (ZMod 2) PUnit.{1} x) f

#print axioms complexConeDescInverseElement
#print axioms complexConeDesc_fst
#print axioms complexConeDesc_snd
#print axioms complexConeDesc_rightInverse
#print axioms complexConeDesc_leftInverse
#print axioms complexConeDesc_bijective
#print axioms complexConeDesc_isIso
#print axioms moduleConeImageComparison_isIso
#print axioms moduleConeImageIso
#print axioms moduleConeImageIso_hom
#print axioms BalancedTensor.rightTensorConeIso
#print axioms moduleRelativeKFlat_cone
