module
public import SerrePositivity.DifferentialGraded.Module.Disk
public import SerrePositivity.DifferentialGraded.Module.Left.CategoryComparison
public import Mathlib.Data.ZMod.Basic

/-! # U10a1：sphere/disk・生成元・微分・自由cellの検証 -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.DifferentialGraded.Checks
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
example (K : Complex A) (n : ℤ) : (complexSphere A n ⟶ K) ≃ complexCycles A K n :=
  complexSphereHomEquiv A K n
example (K : Complex A) (n : ℤ) : (complexDisk A n ⟶ K) ≃ K.X n := complexDiskHomEquiv A K n
example (n : ℤ) : δ (-1) 0 (complexDiskContractingCochain A n) =
    Cochain.ofHom (𝟙 (complexDisk A n)) := complexDiskContracting_d A n
example (n : ℤ) (K : Complex A) : Homotopy (𝟙 (complexDisk A n ⊗ K)) 0 :=
  complexDiskTensorContractingHomotopy A n K
example (x : D) (n : ℤ) (M : ModuleCategory A D) :
    (freeSphere A D x n ⟶ M) ≃ complexCycles A ((moduleEvaluation A D x).obj M) n :=
  freeSphereHomEquiv A D x n M
example (x : D) (n : ℤ) (M : ModuleCategory A D) :
    (freeDisk A D x n ⟶ M) ≃ ((moduleEvaluation A D x).obj M).X n :=
  freeDiskHomEquiv A D x n M
example (x : D) (n : ℤ) (M : ModuleCategory A D) (f : freeDisk A D x n ⟶ M) :
    (freeSphereHomEquiv A D x (n + 1) M (freeCellBoundary A D x n ≫ f)).val =
      ((moduleEvaluation A D x).obj M).d n (n + 1) (freeDiskHomEquiv A D x n M f) :=
  freeCellBoundary_comp A D x n M f
example (x : D) (n : ℤ) : moduleAcyclic A D (freeDisk A D x n) := freeDisk_acyclic A D x n
example (x : D) (n : ℤ) :
    moduleQuasiIso A D (moduleZeroTo A D (freeDisk A D x n)) := freeDisk_zeroTo_quasiIso A D x n
example : Small.{u} (D × ℤ) := inferInstance
example : (complexDisk ℤ (-2)).Acyclic := complexDisk_acyclic ℤ (-2)
example : (complexDisk (ZMod 2) 1).Acyclic := complexDisk_acyclic (ZMod 2) 1
example : moduleQuasiIso ℤ PUnit.{1}
    (moduleZeroTo ℤ PUnit.{1} (freeDisk ℤ PUnit.{1} PUnit.unit (-2))) :=
  freeDisk_zeroTo_quasiIso ℤ PUnit.{1} PUnit.unit (-2)
example : moduleQuasiIso (ZMod 2) PUnit.{1}
    (moduleZeroTo (ZMod 2) PUnit.{1} (freeDisk (ZMod 2) PUnit.{1} PUnit.unit 1)) :=
  freeDisk_zeroTo_quasiIso (ZMod 2) PUnit.{1} PUnit.unit 1
end SerrePositivity.DifferentialGraded.Checks

#print axioms SerrePositivity.DifferentialGraded.moduleElementMap
#print axioms SerrePositivity.DifferentialGraded.moduleElementEquiv
#print axioms SerrePositivity.DifferentialGraded.complexSphere
#print axioms SerrePositivity.DifferentialGraded.complexDisk
#print axioms SerrePositivity.DifferentialGraded.complexCycles
#print axioms SerrePositivity.DifferentialGraded.complexDiskX₀
#print axioms SerrePositivity.DifferentialGraded.complexDiskX₁
#print axioms SerrePositivity.DifferentialGraded.complexDiskHomEquiv
#print axioms SerrePositivity.DifferentialGraded.complexSphereCycle
#print axioms SerrePositivity.DifferentialGraded.complexSphereMap
#print axioms SerrePositivity.DifferentialGraded.complexSphereHomEquiv
#print axioms SerrePositivity.DifferentialGraded.complexSphereToDisk
#print axioms SerrePositivity.DifferentialGraded.complexDiskHomEquiv_apply
#print axioms SerrePositivity.DifferentialGraded.complexDiskHomEquiv_naturality
#print axioms SerrePositivity.DifferentialGraded.complexDisk_upper_apply
#print axioms SerrePositivity.DifferentialGraded.complexSphereToDisk_comp
#print axioms SerrePositivity.DifferentialGraded.complexDiskContractingCochain
#print axioms SerrePositivity.DifferentialGraded.complexDiskContracting_d
#print axioms SerrePositivity.DifferentialGraded.complexDiskContractingHomotopy
#print axioms SerrePositivity.DifferentialGraded.complexDisk_acyclic
#print axioms SerrePositivity.DifferentialGraded.complexDiskTensorContractingHomotopy
#print axioms SerrePositivity.DifferentialGraded.complexDiskTensor_acyclic
#print axioms SerrePositivity.DifferentialGraded.freeSphere
#print axioms SerrePositivity.DifferentialGraded.freeDisk
#print axioms SerrePositivity.DifferentialGraded.freeCellBoundary
#print axioms SerrePositivity.DifferentialGraded.freeSphereHomEquiv
#print axioms SerrePositivity.DifferentialGraded.freeDiskHomEquiv
#print axioms SerrePositivity.DifferentialGraded.freeDiskHomEquiv_naturality
#print axioms SerrePositivity.DifferentialGraded.freeCellBoundary_comp
#print axioms SerrePositivity.DifferentialGraded.freeDisk_acyclic
#print axioms SerrePositivity.DifferentialGraded.freeDisk_zeroTo_quasiIso
