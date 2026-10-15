module
public import SerrePositivity.DifferentialGraded.Module.DiskCover
public import SerrePositivity.DifferentialGraded.Module.Ring
public import Mathlib.Data.ZMod.Basic

/-! # U10a3：自由disk被覆の宇宙と全射性 -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.DifferentialGraded.Checks
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
example (M : ModuleCategory A D) : Small.{u} (ModuleDiskCoverIndex A D M) := inferInstance
example (M : ModuleCategory A D) : moduleDegreewiseSurjective A D (moduleDiskCoverπ A D M) :=
  moduleDiskCoverπ_degreewiseSurjective A D M
example (M : ModuleCategory A D) (x : D) (n : ℤ) :
    Epi (((moduleEvaluation A D x).map (moduleDiskCoverπ A D M)).f n) :=
  (moduleDegreewiseSurjective_iff_epi A D _).1 (moduleDiskCoverπ_degreewiseSurjective A D M) x n
example (M : ModuleCategory ℤ PUnit.{1}) :
    moduleSurjectiveAt ℤ PUnit.{1} PUnit.unit (-2) (moduleDiskCoverπ ℤ PUnit.{1} M) :=
  moduleDiskCoverπ_degreewiseSurjective ℤ PUnit.{1} M PUnit.unit (-2)
example (M : ModuleCategory (ZMod 2) PUnit.{1}) :
    moduleSurjectiveAt (ZMod 2) PUnit.{1} PUnit.unit 1 (moduleDiskCoverπ (ZMod 2) PUnit.{1} M) :=
  moduleDiskCoverπ_degreewiseSurjective (ZMod 2) PUnit.{1} M PUnit.unit 1
end SerrePositivity.DifferentialGraded.Checks

#print axioms SerrePositivity.DifferentialGraded.ModuleDiskCoverIndex
#print axioms SerrePositivity.DifferentialGraded.moduleDiskCoverIndexSmall
#print axioms SerrePositivity.DifferentialGraded.moduleDiskCoverFamily
#print axioms SerrePositivity.DifferentialGraded.moduleDiskCover
#print axioms SerrePositivity.DifferentialGraded.moduleDiskCoverι
#print axioms SerrePositivity.DifferentialGraded.moduleDiskCoverπ
#print axioms SerrePositivity.DifferentialGraded.moduleDiskCoverι_π
#print axioms SerrePositivity.DifferentialGraded.moduleDiskCoverπ_degreewiseSurjective
