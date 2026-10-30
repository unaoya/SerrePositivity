module

public import SerrePositivity.PerfectComplex.IdempotentImagePerfect
public import SerrePositivity.HomologicalAlgebra.Complex.Idempotent

/-! # Images and supported classes of trivial idempotents

The zero and identity cases are shared by involution eigenspaces and cubic character images.
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity
open CategoryTheory Category Limits
variable {R : Type u} [CommRing R]
variable {K : CochainComplex (ModuleCat.{u} R) ℤ}

/-- A zero complex has zero class for any closed support containing its homology. -/
lemma K0WithSupport.mk_eq_zero_of_isZero (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (hp : strictlyPerfectComplex R K) (hs : HasHomologySupportOn Z K) (hz : IsZero K) :
    K0WithSupport.mk Z (supportedPerfectOnObj Z K hp hs) = 0 := by
  have hobj : IsZero (supportedPerfectOnObj Z K hp hs) :=
    IsZero.of_full_of_faithful_of_isZero
      (supportedPerfectOnInclusion Z ⋙ perfectHomotopyInclusion R) _
      ((homotopyQuot R).map_isZero hz)
  exact TriangulatedK0.mk_of_isZero _ hobj

end SerrePositivity
