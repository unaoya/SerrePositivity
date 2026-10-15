module
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Module.Projective

/-! # Projectivity under arbitrary extension of scalars -/
@[expose] public section
universe u
namespace SerrePositivity
variable {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)

/-- Extension of scalars preserves projectivity without a finite-generation hypothesis. -/
lemma projective_baseChange (M : ModuleCat.{u} R) [Module.Projective R M] :
    Module.Projective S ((ModuleCat.extendScalars.{u, u, u} φ).obj M) := by
  let := φ.toAlgebra
  change Module.Projective S (TensorProduct R S M)
  infer_instance

end SerrePositivity
