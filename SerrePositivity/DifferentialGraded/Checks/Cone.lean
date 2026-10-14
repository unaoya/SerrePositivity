module
public import SerrePositivity.DifferentialGraded.Module.Cone
public import SerrePositivity.DifferentialGraded.Module.Ring
public import Mathlib.Data.ZMod.Basic

/-! # U7b3a：cone の全次数作用と objectwise 評価 -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.DifferentialGraded.Checks
open CategoryTheory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
example {M N : ModuleCategory A D} (f : M ⟶ N) (x : D) :
    (moduleEvaluation A D x).obj (moduleCone A D f) =
      mappingCone ((moduleEvaluation A D x).map f) := moduleCone_eval A D f x
example {M N : ModuleCategory A D} (f : M ⟶ N) (x : D) :
    (moduleEvaluation A D x).map (moduleConeInr A D f) =
      mappingCone.inr ((moduleEvaluation A D x).map f) := moduleConeInr_eval A D f x
example {P Q R S : Complex A} (f : P ⟶ Q) (g : R ⟶ S)
    (a : Homogeneous P R 1) (b : Homogeneous Q S 1) :
    (coneMapCochain f g a b).comp (mappingCone.fst g).val rfl =
      -(mappingCone.fst f).val.comp a (by omega : (1 : ℤ) + 1 = 1 + 1) := by
  rw [coneMapCochain_fst]
  simp only [Int.negOnePow_one, Units.neg_smul, one_smul]
example {P Q R S : Complex A} (f : P ⟶ Q) (g : R ⟶ S)
    (a : Homogeneous P R (-1)) (b : Homogeneous Q S (-1)) :
    (coneMapCochain f g a b).comp (mappingCone.fst g).val rfl =
      -(mappingCone.fst f).val.comp a (by omega : (1 : ℤ) + (-1) = (-1) + 1) := by
  rw [coneMapCochain_fst]
  simp only [Int.negOnePow_neg, Int.negOnePow_one, Units.neg_smul, one_smul]
example {P Q R S : Complex A} (f : P ⟶ Q) (g : R ⟶ S) (p : ℤ)
    (a : Homogeneous P R p) (b : Homogeneous Q S p)
    (h : a.comp (Cochain.ofHom g) (add_zero p) =
      (Cochain.ofHom f).comp b (zero_add p)) :
    δ p (p + 1) (coneMapCochain f g a b) =
      coneMapCochain f g (δ p (p + 1) a) (δ p (p + 1) b) :=
  coneMapCochain_differential f g a b h
example {M N : ModuleCategory ℤ PUnit.{1}} (f : M ⟶ N) :
    (moduleEvaluation ℤ PUnit.{1} PUnit.unit).obj (moduleCone ℤ PUnit.{1} f) =
      mappingCone ((moduleEvaluation ℤ PUnit.{1} PUnit.unit).map f) := rfl
example {M N : ModuleCategory (ZMod 2) PUnit.{1}} (f : M ⟶ N) :
    N ⟶ moduleCone (ZMod 2) PUnit.{1} f := moduleConeInr _ _ f
end SerrePositivity.DifferentialGraded.Checks
#print axioms SerrePositivity.DifferentialGraded.coneMapCochain
#print axioms SerrePositivity.DifferentialGraded.coneMapCochain_fst
#print axioms SerrePositivity.DifferentialGraded.coneMapCochain_snd
#print axioms SerrePositivity.DifferentialGraded.coneMapCochain_v
#print axioms SerrePositivity.DifferentialGraded.coneMapCochain_add
#print axioms SerrePositivity.DifferentialGraded.coneMapCochain_smul
#print axioms SerrePositivity.DifferentialGraded.coneMapCochain_units_smul
#print axioms SerrePositivity.DifferentialGraded.coneMapCochain_identity
#print axioms SerrePositivity.DifferentialGraded.coneMapCochain_differential
#print axioms SerrePositivity.DifferentialGraded.coneMapCochain_comp
#print axioms SerrePositivity.DifferentialGraded.coneMapCochain_inr
#print axioms SerrePositivity.DifferentialGraded.coneHom_square_apply
#print axioms SerrePositivity.DifferentialGraded.coneHomMap
#print axioms SerrePositivity.DifferentialGraded.coneHomMap_apply
#print axioms SerrePositivity.DifferentialGraded.coneHomMap_inr
#print axioms SerrePositivity.DifferentialGraded.moduleMap_unit_cochain
#print axioms SerrePositivity.DifferentialGraded.moduleMap_forward
#print axioms SerrePositivity.DifferentialGraded.coneModule
#print axioms SerrePositivity.DifferentialGraded.moduleCone
#print axioms SerrePositivity.DifferentialGraded.moduleCone_eval
#print axioms SerrePositivity.DifferentialGraded.moduleConeInr
#print axioms SerrePositivity.DifferentialGraded.moduleConeInr_eval
