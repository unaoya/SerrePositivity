module
public import SerrePositivity.DifferentialGraded.Module.Disk
public import SerrePositivity.DifferentialGraded.Module.Left.CategoryComparison
public import Mathlib.Data.ZMod.Basic

/-! # U8a1/b1：加群ホモトピーと objectwise quasiIso の受入入口 -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.DifferentialGraded.Checks
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {M N P : ModuleCategory A D} (f : M ⟶ N) (g : N ⟶ P)

example : Linear A (ModuleHomotopyCategory A D) := inferInstance
example : (moduleToHomotopy A D).Additive := inferInstance
example : (moduleToHomotopy A D).Linear A := inferInstance
example (f' : M ⟶ N) :
    (moduleToHomotopy A D).map f = (moduleToHomotopy A D).map f' ↔
      Nonempty (ModuleHomotopy A D f f') := moduleToHomotopy_map_eq_iff A D f f'
example (f' : M ⟶ N) (h : ModuleHomotopy A D f f') (x : D) :
    Nonempty (Homotopy ((moduleEvaluation A D x).map f)
      ((moduleEvaluation A D x).map f')) := moduleHomotopy_evaluation A D h x
example (f' : M ⟶ N) (h : ModuleHomotopy A D f f') :
    moduleQuasiIso A D f ↔ moduleQuasiIso A D f' := moduleQuasiIso_iff_of_homotopy A D h
example (hf : moduleQuasiIso A D f) (hfg : moduleQuasiIso A D (f ≫ g)) :
    moduleQuasiIso A D g :=
  (moduleQuasiIso A D).of_precomp (W' := moduleQuasiIso A D) f g hf hfg
example (hg : moduleQuasiIso A D g) (hfg : moduleQuasiIso A D (f ≫ g)) :
    moduleQuasiIso A D f :=
  (moduleQuasiIso A D).of_postcomp (W' := moduleQuasiIso A D) f g hg hfg
example : (moduleQuasiIso A D).IsStableUnderRetracts := inferInstance
example : (moduleQuasiIso A D).RespectsIso := inferInstance
example : (moduleHomotopyQuasiIso A D).IsMultiplicative := inferInstance
example : (moduleHomotopyQuasiIso A D).HasTwoOutOfThreeProperty := inferInstance
example : (moduleHomotopyQuasiIso A D).IsStableUnderRetracts := inferInstance
example : (moduleHomotopyQuasiIso A D).RespectsIso := inferInstance
example : moduleHomotopyQuasiIso A D ((moduleToHomotopy A D).map f) ↔
    moduleQuasiIso A D f := moduleHomotopyQuasiIso_map_iff A D f

-- 一対象環では、quasiIso 判定は既存非有界複体の判定そのもの。
example {M N : ModuleCategory ℤ PUnit.{1}} (f : M ⟶ N) :
    moduleQuasiIso ℤ PUnit.{1} f ↔
      QuasiIso ((moduleEvaluation ℤ PUnit.{1} PUnit.unit).map f) := by
  constructor
  · exact fun h => h PUnit.unit
  · intro h x
    cases x
    exact h
example {M N : ModuleCategory (ZMod 2) PUnit.{1}} (f : M ⟶ N) :
    moduleQuasiIso (ZMod 2) PUnit.{1} f ↔
      QuasiIso ((moduleEvaluation (ZMod 2) PUnit.{1} PUnit.unit).map f) := by
  constructor
  · exact fun h => h PUnit.unit
  · intro h x
    cases x
    exact h
end SerrePositivity.DifferentialGraded.Checks

#print axioms SerrePositivity.DifferentialGraded.ModuleHomotopy
#print axioms SerrePositivity.DifferentialGraded.moduleHomotopy_nonempty_iff
#print axioms SerrePositivity.DifferentialGraded.ModuleHomotopyCategory
#print axioms SerrePositivity.DifferentialGraded.moduleToHomotopy
#print axioms SerrePositivity.DifferentialGraded.moduleToHomotopy_map_eq_iff
#print axioms SerrePositivity.DifferentialGraded.moduleHomotopy_evaluation
#print axioms SerrePositivity.DifferentialGraded.moduleHomotopyEvaluation
#print axioms SerrePositivity.DifferentialGraded.moduleHomotopyEvaluation_fac
#print axioms SerrePositivity.DifferentialGraded.moduleQuasiIso
#print axioms SerrePositivity.DifferentialGraded.moduleQuasiIso_eq_iInf
#print axioms SerrePositivity.DifferentialGraded.moduleQuasiIsoIsMultiplicative
#print axioms SerrePositivity.DifferentialGraded.moduleQuasiIsoHasTwoOutOfThree
#print axioms SerrePositivity.DifferentialGraded.moduleQuasiIsoStableUnderRetracts
#print axioms SerrePositivity.DifferentialGraded.moduleQuasiIsoRespectsIso
#print axioms SerrePositivity.DifferentialGraded.moduleQuasiIso_evaluation
#print axioms SerrePositivity.DifferentialGraded.moduleHomotopy_homologyMap_eq
#print axioms SerrePositivity.DifferentialGraded.moduleQuasiIso_iff_of_homotopy
#print axioms SerrePositivity.DifferentialGraded.moduleQuasiIso_iff_of_homotopy_map_eq
#print axioms SerrePositivity.DifferentialGraded.moduleHomotopyQuasiIso
#print axioms SerrePositivity.DifferentialGraded.moduleHomotopyHomology
#print axioms SerrePositivity.DifferentialGraded.moduleHomotopyQuasiIso_eq_iInf
#print axioms SerrePositivity.DifferentialGraded.moduleHomotopyQuasiIsoIsMultiplicative
#print axioms SerrePositivity.DifferentialGraded.moduleHomotopyQuasiIsoHasTwoOutOfThree
#print axioms SerrePositivity.DifferentialGraded.moduleHomotopyQuasiIsoStableUnderRetracts
#print axioms SerrePositivity.DifferentialGraded.moduleHomotopyQuasiIsoRespectsIso
#print axioms SerrePositivity.DifferentialGraded.moduleHomotopyQuasiIso_map_iff
#print axioms SerrePositivity.DifferentialGraded.moduleHomotopyQuasiIso_inverseImage
