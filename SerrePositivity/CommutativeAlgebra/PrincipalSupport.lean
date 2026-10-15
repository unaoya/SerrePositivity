module
public import SerrePositivity.CommutativeAlgebra.ClosedSupportGeometry

/-! # Combining principal supports in an additive family -/
@[expose] public section
universe u v
namespace SerrePositivity
variable {R : Type u} [CommRing R]

/-- Compatible support enlargement combines two denominators by their product. -/
lemma principalSupport_add
    (F : TopologicalSpace.Closeds (PrimeSpectrum R) → Type v) [∀ W, AddCommGroup (F W)]
    (enlarge : ∀ {U V}, U ≤ V → F U →+ F V)
    (hcomp : ∀ {U V W} (h : U ≤ V) (h' : V ≤ W) (y : F U),
      enlarge h' (enlarge h y) = enlarge (h.trans h') y)
    {P : Submonoid R} {Z : TopologicalSpace.Closeds (PrimeSpectrum R)} {x x' : F Z}
    (hx : ∃ s ∈ P, ∃ y : F (Z ⊓ supportZeroLocus (Ideal.span ({s} : Set R))),
      enlarge inf_le_left y = x)
    (hx' : ∃ t ∈ P, ∃ y : F (Z ⊓ supportZeroLocus (Ideal.span ({t} : Set R))),
      enlarge inf_le_left y = x') :
    ∃ s ∈ P, ∃ y : F (Z ⊓ supportZeroLocus (Ideal.span ({s} : Set R))),
      enlarge inf_le_left y = x + x' := by
  obtain ⟨s, hs, y, hy⟩ := hx
  obtain ⟨t, ht, y', hy'⟩ := hx'
  let h₁ := inf_le_inf_left Z (supportZeroLocus_mul_left s t)
  let h₂ := inf_le_inf_left Z (supportZeroLocus_mul_right s t)
  refine ⟨s * t, P.mul_mem hs ht, enlarge h₁ y + enlarge h₂ y', ?_⟩
  rw [map_add, hcomp, hcomp, hy, hy']

end SerrePositivity
