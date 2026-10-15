module
public import SerrePositivity.DifferentialGraded.Derived.HomotopicallyProjective
public import SerrePositivity.DifferentialGraded.Module.FreeHom
public import SerrePositivity.DifferentialGraded.Module.Cells
public import SerrePositivity.DifferentialGraded.Complexes.SphereHom

/-! # 自由sphereはHom endの意味でhomotopically projective

各評価のK-projective性ではなく、free/evaluationの全次数Hom同型から証明する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma freeSphere_homotopicallyProjective (x : D) (n : ℤ) :
    moduleHomotopicallyProjective A D (freeSphere A D x n) := by
  intro N hN i
  exact (complexSphereHom_acyclic A ((moduleEvaluation A D x).obj N) n (hN x) i).of_iso
    (freeHomIso A D x (complexSphere A n) (ForgetEnrichment.to (Complex A) N)).symm

end SerrePositivity.DifferentialGraded
