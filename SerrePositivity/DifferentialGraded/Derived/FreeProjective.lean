module
public import SerrePositivity.DifferentialGraded.Derived.HomotopicallyProjective
public import SerrePositivity.DifferentialGraded.Module.FreeHom
public import SerrePositivity.DifferentialGraded.Complexes.KProjectiveHom

/-! K-projective 係数を持つ自由 dg 加群の全 Hom 射影性。 -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma freeAt_homotopicallyProjective (x : D) (K : Complex A) [K.IsKProjective] :
    moduleHomotopicallyProjective A D ((freeAt x).obj K) := by
  intro N hN
  exact cochainAcyclic_of_iso
    (homComplex_acyclic_of_isKProjective A K ((moduleEvaluation A D x).obj N) (hN x))
    (freeHomIso A D x K (ForgetEnrichment.to (Complex A) N)).symm

end SerrePositivity.DifferentialGraded
