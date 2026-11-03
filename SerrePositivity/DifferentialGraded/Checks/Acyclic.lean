module
public import SerrePositivity.DifferentialGraded.Module.Disk
public import SerrePositivity.DifferentialGraded.Module.Left.CategoryComparison
public import Mathlib.Data.ZMod.Basic

/-! # U8b2：標準加群 cone の objectwise acyclic 性と quasiIso -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.DifferentialGraded.Checks
open CategoryTheory Limits HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
example {P Q : Complex A} (f : P ⟶ Q) :
    QuasiIso f ↔ (CochainComplex.mappingCone f).Acyclic :=
  complex_quasiIso_iff_acyclic_cone A f
example {M N : ModuleCategory A D} (f : M ⟶ N) :
    moduleQuasiIso A D f ↔ moduleAcyclic A D (moduleCone A D f) :=
  moduleQuasiIso_iff_acyclic_cone A D f
example {M N : ModuleCategory A D} (f : M ⟶ N) :
    moduleHomotopyQuasiIso A D ((moduleToHomotopy A D).map f) ↔
      moduleHomotopyAcyclic A D ((moduleToHomotopy A D).obj (moduleCone A D f)) :=
  moduleHomotopyQuasiIso_iff_acyclic_cone A D f
example (M : ModuleHomotopyCategory A D) :
    moduleHomotopyAcyclic A D M ↔ ∀ (x : D) (i : ℤ),
      IsZero ((moduleHomotopyHomology A D x i).obj M) := moduleHomotopyAcyclic_iff A D M
example (M : ModuleCategory A D) :
    moduleHomotopyAcyclic A D ((moduleToHomotopy A D).obj M) ↔ moduleAcyclic A D M :=
  moduleHomotopyAcyclic_obj_iff A D M
example (M : ModuleCategory A D) : moduleAcyclic A D (moduleCone A D (𝟙 M)) :=
  (moduleQuasiIso_iff_acyclic_cone A D _).1 ((moduleQuasiIso A D).id_mem M)
example (M : ModuleCategory ℤ PUnit.{1}) :
    moduleAcyclic ℤ PUnit.{1} (moduleCone ℤ PUnit.{1} (𝟙 M)) :=
  (moduleQuasiIso_iff_acyclic_cone ℤ PUnit.{1} _).1
    ((moduleQuasiIso ℤ PUnit.{1}).id_mem M)
example (M : ModuleCategory (ZMod 2) PUnit.{1}) :
    moduleAcyclic (ZMod 2) PUnit.{1} (moduleCone (ZMod 2) PUnit.{1} (𝟙 M)) :=
  (moduleQuasiIso_iff_acyclic_cone (ZMod 2) PUnit.{1} _).1
    ((moduleQuasiIso (ZMod 2) PUnit.{1}).id_mem M)
end SerrePositivity.DifferentialGraded.Checks

#print axioms SerrePositivity.DifferentialGraded.complex_quasiIso_iff_acyclic_cone
#print axioms SerrePositivity.DifferentialGraded.moduleAcyclic
#print axioms SerrePositivity.DifferentialGraded.moduleAcyclic_iff
#print axioms SerrePositivity.DifferentialGraded.moduleHomotopyAcyclic
#print axioms SerrePositivity.DifferentialGraded.moduleHomotopyAcyclic_obj_iff
#print axioms SerrePositivity.DifferentialGraded.moduleHomotopyAcyclic_iff
#print axioms SerrePositivity.DifferentialGraded.moduleQuasiIso_iff_acyclic_cone
#print axioms SerrePositivity.DifferentialGraded.moduleHomotopyQuasiIso_iff_acyclic_cone
