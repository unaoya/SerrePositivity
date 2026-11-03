module
public import SerrePositivity.DifferentialGraded.Module.Disk
public import SerrePositivity.DifferentialGraded.Module.Left.CategoryComparison
public import Mathlib.Data.ZMod.Basic

/-! # U10a2：I/Jの具体的右liftクラスと非有界複体の準同型判定 -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.DifferentialGraded.Checks
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {M N : ModuleCategory A D} (f : M ⟶ N)
example (x : D) (n : ℤ) :
    HasLiftingProperty (moduleZeroTo A D (freeDisk A D x n)) f ↔ moduleSurjectiveAt A D x n f :=
  freeDisk_lifting_iff_surjective A D x n f
example : (freeDiskInclusions A D).rlp = moduleDegreewiseSurjective A D :=
  freeDiskInclusions_rlp_eq A D
example : moduleDegreewiseSurjective A D f ↔ ∀ (x : D) (n : ℤ),
    Epi (((moduleEvaluation A D x).map f).f n) := moduleDegreewiseSurjective_iff_epi A D f
example (x : D) (n : ℤ) :
    HasLiftingProperty (freeCellBoundary A D x n) f ↔ moduleBoundaryLiftAt A D x n f :=
  freeCellBoundary_lifting_iff A D x n f
example : (freeCellBoundaries A D).rlp =
    moduleDegreewiseSurjective A D ⊓ moduleQuasiIso A D := freeCellBoundaries_rlp_eq A D
example (h : (freeCellBoundaries A D).rlp f) : moduleQuasiIso A D f :=
  moduleQuasiIso_of_boundary_lifting A D f ((freeCellBoundaries_rlp_iff A D f).1 h)
example (hs : moduleDegreewiseSurjective A D f) (hq : moduleQuasiIso A D f) (x : D) (n : ℤ) :
    HasLiftingProperty (freeCellBoundary A D x n) f :=
  (freeCellBoundary_lifting_iff A D x n f).2
    (moduleBoundaryLiftAt_of_surjective_quasiIso A D f hs hq x n)
example : (moduleDegreewiseSurjective A D).IsStableUnderRetracts := inferInstance
example : (moduleDegreewiseSurjective A D).RespectsIso := inferInstance
example {M N : ModuleCategory ℤ PUnit.{1}} (f : M ⟶ N)
    (hs : moduleDegreewiseSurjective ℤ PUnit.{1} f) (hq : moduleQuasiIso ℤ PUnit.{1} f) :
    HasLiftingProperty (freeCellBoundary ℤ PUnit.{1} PUnit.unit (-2)) f :=
  (freeCellBoundary_lifting_iff ℤ PUnit.{1} PUnit.unit (-2) f).2
    (moduleBoundaryLiftAt_of_surjective_quasiIso ℤ PUnit.{1} f hs hq PUnit.unit (-2))
example {M N : ModuleCategory (ZMod 2) PUnit.{1}} (f : M ⟶ N)
    (hs : moduleDegreewiseSurjective (ZMod 2) PUnit.{1} f)
    (hq : moduleQuasiIso (ZMod 2) PUnit.{1} f) :
    HasLiftingProperty (freeCellBoundary (ZMod 2) PUnit.{1} PUnit.unit 1) f :=
  (freeCellBoundary_lifting_iff (ZMod 2) PUnit.{1} PUnit.unit 1 f).2
    (moduleBoundaryLiftAt_of_surjective_quasiIso (ZMod 2) PUnit.{1} f hs hq PUnit.unit 1)
end SerrePositivity.DifferentialGraded.Checks

#print axioms SerrePositivity.DifferentialGraded.moduleSurjectiveAt
#print axioms SerrePositivity.DifferentialGraded.moduleDegreewiseSurjective
#print axioms SerrePositivity.DifferentialGraded.moduleSurjectiveAt_iff_epi
#print axioms SerrePositivity.DifferentialGraded.freeDisk_lifting_iff_surjective
#print axioms SerrePositivity.DifferentialGraded.freeDiskInclusions
#print axioms SerrePositivity.DifferentialGraded.freeDiskInclusions_rlp_iff
#print axioms SerrePositivity.DifferentialGraded.freeDiskInclusions_rlp_eq
#print axioms SerrePositivity.DifferentialGraded.moduleDegreewiseSurjective_iff_epi
#print axioms SerrePositivity.DifferentialGraded.moduleDegreewiseSurjectiveStableUnderRetracts
#print axioms SerrePositivity.DifferentialGraded.moduleDegreewiseSurjectiveRespectsIso
#print axioms SerrePositivity.DifferentialGraded.complexSphereHomEquiv_naturality_val
#print axioms SerrePositivity.DifferentialGraded.freeSphereHomEquiv_naturality_val
#print axioms SerrePositivity.DifferentialGraded.moduleBoundaryLiftAt
#print axioms SerrePositivity.DifferentialGraded.freeCellBoundary_lifting_iff
#print axioms SerrePositivity.DifferentialGraded.moduleSurjectiveAt_of_boundary_lifting
#print axioms SerrePositivity.DifferentialGraded.freeCellBoundaries
#print axioms SerrePositivity.DifferentialGraded.freeCellBoundaries_rlp_iff
#print axioms SerrePositivity.DifferentialGraded.freeCellBoundaries_rlp_degreewiseSurjective
#print axioms SerrePositivity.DifferentialGraded.complexBoundaryLiftAt
#print axioms SerrePositivity.DifferentialGraded.complexCone_element_ext
#print axioms SerrePositivity.DifferentialGraded.complex_quasiIso_of_boundary_lifting
#print axioms SerrePositivity.DifferentialGraded.complex_boundary_lifting_of_surjective_quasiIso
#print axioms SerrePositivity.DifferentialGraded.moduleQuasiIso_of_boundary_lifting
#print axioms SerrePositivity.DifferentialGraded.moduleBoundaryLiftAt_of_surjective_quasiIso
#print axioms SerrePositivity.DifferentialGraded.freeCellBoundaries_rlp_eq
