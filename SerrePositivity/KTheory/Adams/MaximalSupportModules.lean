module

public import SerrePositivity.KTheory.MaximalSupportModules
public import SerrePositivity.CommutativeAlgebra.SemilocalSupport

/-! # Finite length on least-height localization -/

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

/-- The support identified by least-height localization consists of finite-length modules. -/
lemma HeightAtLeast.localized_module_finiteLength (h : HeightAtLeast Z c)
    (M : SupportedFGModuleOn (supportPullback (algebraMap R B) Z)) :
    IsFiniteLength B M.obj := by
  let := IsLocalization.isNoetherianRing (heightStratumComplement Z c) B
    (inferInstance : IsNoetherianRing R)
  exact finiteLength_of_maximal_support _
    (fun p hp => (h.mem_pullback_iff_isMaximal p).mp hp) M

end Adams
end SerrePositivity
