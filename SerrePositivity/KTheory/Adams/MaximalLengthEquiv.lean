module

public import SerrePositivity.KTheory.MaximalSupportLengthEquiv
public import SerrePositivity.KTheory.MaximalSupportLocalLength
public import SerrePositivity.KTheory.Adams.MaximalSupportModules

/-! # Length coordinates on least-height localization -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
namespace Adams
variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {B : Type u} [CommRing B] [Algebra R B]
variable {Z : TopologicalSpace.Closeds (PrimeSpectrum R)} {c : ℕ}
variable [IsLocalization (heightStratumComplement Z c) B]

/-- The least-height localization admits the local-length coordinate isomorphism. -/
def HeightAtLeast.semilocalLengthEquiv (h : HeightAtLeast Z c) :
    G0WithSupport (supportPullback (algebraMap R B) Z) ≃+
      ({q : PrimeSpectrum B // q ∈ supportPullback (algebraMap R B) Z} → ℤ) := by
  let := IsLocalization.isNoetherianRing (heightStratumComplement Z c) B
    (inferInstance : IsNoetherianRing R)
  have hf : (supportPullback (algebraMap R B) Z : Set (PrimeSpectrum B)).Finite :=
    h.finite_localized_maximal_points.subset
      (fun q hq => (h.mem_pullback_iff_isMax q).mp hq)
  letI := hf.fintype
  exact maximalLengthEquiv _ (fun q hq => (h.mem_pullback_iff_isMaximal q).mp hq)

end Adams
end SerrePositivity
