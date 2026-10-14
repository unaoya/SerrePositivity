module
public import SerrePositivity.DifferentialGraded.Module.FreeHom
public import Mathlib.Data.ZMod.Basic

/-! # 自由加群の全次数 Hom 複体同型の受入検証 -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.DifferentialGraded.Checks
open CategoryTheory MonoidalCategory HomologicalComplex Opposite
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D] [Small.{u} D]
example (x : D) (K : Complex A) (M : RightModule A D) :
    moduleHom A D (freeModule x K) M ≅ homComplex A K (M.obj (op x)) :=
  freeHomIso A D x K M
example (x : D) (K : Complex A) (M : RightModule A D) :
    (freeHomIso A D x K M).hom ≫ (freeHomIso A D x K M).inv = 𝟙 _ :=
  (freeHomIso A D x K M).hom_inv_id
example (x : D) (K : Complex A) (M : RightModule A D) :
    (freeHomIso A D x K M).inv ≫ (freeHomIso A D x K M).hom = 𝟙 _ :=
  (freeHomIso A D x K M).inv_hom_id
example (x : D) (K : Complex A) (M : RightModule A D) (y : Dᵒᵖ)
    (ψ : Homogeneous K (M.obj (op x)) (-1)) (t : K.X 1)
    (h : GradedHom A y.unop x 1) :
    ((freeExtensionApp A x K M y).f (-1) ψ).v 2 1 (by omega)
      (ιTensorObj K (y.unop ⟶[Complex A] x) 1 1 2 rfl (t ⊗ₜ[A] h)) =
    ((-1 + 1) * 1 : ℤ).negOnePow • moduleAction A M (x := op x) (y := y) h
      (ψ.v 1 0 (by omega) t) (by omega) :=
  freeExtensionApp_apply A x K M y (-1) 1 1 2 1 rfl (by omega) ψ t h
example (K : Complex (ZMod 2)) (M : RightModule (ZMod 2) PUnit.{1}) :
    moduleHom (ZMod 2) PUnit.{1} (freeModule PUnit.unit K) M ≅
      homComplex (ZMod 2) K (M.obj (op PUnit.unit)) :=
  freeHomIso (ZMod 2) PUnit.{1} PUnit.unit K M
end SerrePositivity.DifferentialGraded.Checks
#print axioms SerrePositivity.DifferentialGraded.moduleParamNaturality_of_cochain
#print axioms SerrePositivity.DifferentialGraded.freeExtensionApp_apply
#print axioms SerrePositivity.DifferentialGraded.freeExtensionApp_naturality
#print axioms SerrePositivity.DifferentialGraded.freeFamilyEvaluation_extension
#print axioms SerrePositivity.DifferentialGraded.freeFamilyEvaluation_restore
#print axioms SerrePositivity.DifferentialGraded.freeHomIso
