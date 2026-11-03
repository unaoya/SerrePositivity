module
public import SerrePositivity.DifferentialGraded.Module.Disk
public import SerrePositivity.DifferentialGraded.Module.Left.CategoryComparison
public import Mathlib.Data.ZMod.Basic

/-! # U10a9：自由diskの二段sphere filtration -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.DifferentialGraded.Checks
open CategoryTheory Limits Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
example (x : D) (n : ℤ) :
    ModuleGradedSplit A D (freeCellBoundary A D x n) (freeDiskToSphere A D x n) :=
  freeDiskGradedSplit A D x n
example (x : D) (n : ℤ) : Mono (freeCellBoundary A D x n) := freeCellBoundary_mono A D x n
example (x : D) (n : ℤ) : Epi (freeDiskToSphere A D x n) := freeDiskToSphere_epi A D x n
example (x : D) (n : ℤ) :
    IsColimit (CokernelCofork.ofπ (freeDiskToSphere A D x n) (freeCellBoundary_toSphere A D x n)) :=
  freeDiskSphereCokernel A D x n
example (x y : D) (n k : ℤ) :
    ((freeDiskGradedSplit A D x n).evaluationShortComplex y k).ShortExact :=
  (freeDiskGradedSplit A D x n).evaluationShortExact y k
example (x y z : D) (n p i j : ℤ) (hij : i + p = j)
    (a : GradedHom A (op y) (op z) p) :
    moduleActionComponent A D (freeDisk A D x n) y z p i j hij a ≫
        (freeDiskGradedSplit A D x n).retraction z j =
      (freeDiskGradedSplit A D x n).retraction y i ≫
        moduleActionComponent A D (freeSphere A D x (n + 1)) y z p i j hij a :=
  (freeDiskGradedSplit A D x n).retraction_naturality y z p i j hij a
example : Mono (freeCellBoundary ℤ PUnit.{1} PUnit.unit (-2)) :=
  freeCellBoundary_mono ℤ PUnit.{1} PUnit.unit (-2)
example : Epi (freeDiskToSphere (ZMod 2) PUnit.{1} PUnit.unit 1) :=
  freeDiskToSphere_epi (ZMod 2) PUnit.{1} PUnit.unit 1
example (n k : ℤ) :
    ((complexDiskSphereShortComplex A n).map
      (HomologicalComplex.eval (ModuleCat A) (.up ℤ) k)).ShortExact :=
  complexDiskSphereShortExact A n k
end SerrePositivity.DifferentialGraded.Checks

#print axioms SerrePositivity.DifferentialGraded.complexDiskToSphere
#print axioms SerrePositivity.DifferentialGraded.complexDiskToSphere_f
#print axioms SerrePositivity.DifferentialGraded.complexDiskToSphere_f_eq_zero
#print axioms SerrePositivity.DifferentialGraded.complexSphereToDisk_f
#print axioms SerrePositivity.DifferentialGraded.complexSphereToDisk_f_eq_zero
#print axioms SerrePositivity.DifferentialGraded.complexSphereToDiskToSphere
#print axioms SerrePositivity.DifferentialGraded.complexDiskGradedRetraction
#print axioms SerrePositivity.DifferentialGraded.complexDiskGradedSection
#print axioms SerrePositivity.DifferentialGraded.complexDiskGraded_inclusion_retraction
#print axioms SerrePositivity.DifferentialGraded.complexDiskGraded_section_projection
#print axioms SerrePositivity.DifferentialGraded.complexDiskGraded_section_retraction
#print axioms SerrePositivity.DifferentialGraded.complexDiskGraded_decomposition
#print axioms SerrePositivity.DifferentialGraded.complexDiskSphereShortComplex
#print axioms SerrePositivity.DifferentialGraded.complexDiskSphereSplitting
#print axioms SerrePositivity.DifferentialGraded.complexDiskSphereShortExact
#print axioms SerrePositivity.DifferentialGraded.complexDiskGraded_inclusion_retraction_cochain
#print axioms SerrePositivity.DifferentialGraded.complexDiskGraded_section_projection_cochain
#print axioms SerrePositivity.DifferentialGraded.complexDiskGraded_section_retraction_cochain
#print axioms SerrePositivity.DifferentialGraded.complexDiskGraded_decomposition_cochain
#print axioms SerrePositivity.DifferentialGraded.tensorGradedZeroComponent
#print axioms SerrePositivity.DifferentialGraded.ι_tensorGradedZero
#print axioms SerrePositivity.DifferentialGraded.tensorGradedZeroComponent_ofHom
#print axioms SerrePositivity.DifferentialGraded.tensorGradedZeroComponent_add
#print axioms SerrePositivity.DifferentialGraded.tensorGradedZeroComponent_zero
#print axioms SerrePositivity.DifferentialGraded.tensorGradedZeroComponent_comp
#print axioms SerrePositivity.DifferentialGraded.tensorGradedZeroComponent_id
#print axioms SerrePositivity.DifferentialGraded.tensorGradedZeroComponent_apply
#print axioms SerrePositivity.DifferentialGraded.tensorGradedZeroComponent_naturality
#print axioms SerrePositivity.DifferentialGraded.freeDiskToSphere
#print axioms SerrePositivity.DifferentialGraded.freeDiskToSphere_eval
#print axioms SerrePositivity.DifferentialGraded.freeCellBoundary_eval
#print axioms SerrePositivity.DifferentialGraded.freeCellBoundary_toSphere
#print axioms SerrePositivity.DifferentialGraded.freeDiskGradedSplit
#print axioms SerrePositivity.DifferentialGraded.freeCellBoundary_mono
#print axioms SerrePositivity.DifferentialGraded.freeDiskToSphere_epi
#print axioms SerrePositivity.DifferentialGraded.freeDiskSphereCokernel
