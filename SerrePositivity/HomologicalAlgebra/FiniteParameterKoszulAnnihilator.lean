module
public import SerrePositivity.HomologicalAlgebra.ParameterKoszulIdempotent
public import SerrePositivity.CommutativeAlgebra.ParameterRadicalImage

/-! # Actual positive Koszul annihilation for finite-stage parameters -/
@[expose] public noncomputable section
universe u
namespace SerrePositivity
open CategoryTheory

/-- A finite injective local extension supplies the parameter support conditions. The
annihilator is the original base ideal, acting by restriction along its actual coefficient map.
The distinguished scalar is allowed to be any one of the standard coordinates. -/
lemma finiteParameterKoszul_positive_annihilator
    {R D E C S : Type u} [CommRing R] [CommRing D] [CommRing E] [CommRing C] [CommRing S]
    [IsNoetherian R R] [IsLocalRing D] [IsLocalRing E]
    [Algebra R D] [Algebra D E] [Module.Finite D E] [Algebra R C]
    (hinj : Function.Injective (algebraMap D E)) (φ : E →+* C)
    (hφ : ∀ x : R, φ (algebraMap D E (algebraMap R D x)) = algebraMap R C x)
    {e : ℕ} (z : Fin e → R)
    (hz : IsSystemOfParameters D (algebraMap R D ∘ z))
    (hres : ∀ n : ℕ, IsKoszulResolution (fun j => z j ^ n))
    (ψ : S →+* C) (I : Ideal S) (a : S) (j₀ : Fin e)
    (ha : ψ a = algebraMap R C (z j₀))
    (hI : ∀ n : ℕ, 0 < n →
      IsIdempotentElem (I.map (Ideal.Quotient.mk (Ideal.span {a ^ n}))))
    (hTor : ∀ (N : ModuleCat.{u} R) (j : ℕ), 0 < j →
      ∀ s ∈ I, torCoefficientScalarEndomorphism C N j (ψ s) = 0)
    (y : Fin e → E) (hy : IsSystemOfParameters E y) (i : ℕ) (hi : 0 < i) :
    let _ := Module.compHom (koszulHomologySelf (φ ∘ y) i) ψ
    I ≤ Module.annihilator S (koszulHomologySelf (φ ∘ y) i) := by
  have hsupport : ∀ j, algebraMap R C (z j) ∈
      (Ideal.span (Set.range (φ ∘ y))).radical := by
    intro j
    simpa only [Function.comp_apply, hφ] using
      hz.finite_map_coordinates_mem_radical hinj hy φ j
  exact parameterKoszulPositiveHomology_restricted_annihilator_of_tor_and_idempotent
    ψ I a z (φ ∘ y) hsupport hres hTor (by rw [ha]; exact hsupport j₀) hI i hi

end SerrePositivity
