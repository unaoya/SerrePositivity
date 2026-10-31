module
public import SerrePositivity.DifferentialGraded
public import Mathlib.Data.ZMod.Basic

/-! # U6 の自由 Hom 同型の自然性・閉零随伴比較の受入検証 -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.DifferentialGraded.Checks
open CategoryTheory MonoidalCategory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
example (x : D) (K : Complex A) {M N : ModuleCategory A D} (f : M ⟶ N) :
    eHomWhiskerLeft (Complex A) ((freeAt x).obj K) f ≫
      (freeHomIso A D x K (ForgetEnrichment.to (Complex A) N)).hom =
    (freeHomIso A D x K (ForgetEnrichment.to (Complex A) M)).hom ≫
      homPostcompose K ((moduleEvaluation A D x).map f) :=
  freeHomIso_naturality_target A D x K f
example (x : D) {K L : Complex A} (g : L ⟶ K) (M : ModuleCategory A D) :
    eHomWhiskerRight (Complex A) ((freeAt x).map g) M ≫
      (freeHomIso A D x L (ForgetEnrichment.to (Complex A) M)).hom =
    (freeHomIso A D x K (ForgetEnrichment.to (Complex A) M)).hom ≫
      homPrecompose g ((moduleEvaluation A D x).obj M) :=
  freeHomIso_naturality_source A D x g M
example (x : D) (K : Complex A) (M : ModuleCategory A D) (f : (freeAt x).obj K ⟶ M) :
    mapFromUnit A K ((ForgetEnrichment.to (Complex A) M).obj (op x))
      (ForgetEnrichment.homTo (Complex A) (C := RightModule A D)
          (X := (freeAt x).obj K) (Y := M) f ≫
        (freeHomIso A D x K (ForgetEnrichment.to (Complex A) M)).hom) =
      freeHomEquiv A D x K M f := freeHomIso_closed_zero A D x K M f
example : freeAt (A := ℤ) PUnit.unit ⊣ moduleEvaluation ℤ PUnit.{1} PUnit.unit :=
  freeEvaluationAdjunction ℤ PUnit.{1} PUnit.unit
example (K : Complex (ZMod 2)) (M : RightModule (ZMod 2) PUnit.{1}) :
    moduleHom (ZMod 2) PUnit.{1} (freeModule PUnit.unit K) M ≅
      homComplex (ZMod 2) K (M.obj (op PUnit.unit)) :=
  freeHomIso (ZMod 2) PUnit.{1} PUnit.unit K M
end SerrePositivity.DifferentialGraded.Checks
#print axioms SerrePositivity.DifferentialGraded.tensorModule_eq_comp
#print axioms SerrePositivity.DifferentialGraded.complexHomWhiskerLeft
#print axioms SerrePositivity.DifferentialGraded.complexHomWhiskerRight
#print axioms SerrePositivity.DifferentialGraded.moduleHomWhiskerLeft_π
#print axioms SerrePositivity.DifferentialGraded.moduleHomWhiskerRight_π
#print axioms SerrePositivity.DifferentialGraded.freeHomIso_naturality_target
#print axioms SerrePositivity.DifferentialGraded.freeHomIso_naturality_source
#print axioms SerrePositivity.DifferentialGraded.freeHomIso_closed_zero
