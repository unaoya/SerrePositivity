module
public import SerrePositivity.CommutativeAlgebra.AbsolutelyIntegrallyClosedEtale
public import SerrePositivity.CommutativeAlgebra.PrincipalAlgebraIsomorphismLocus

/-! # A finite principal splitting cover of an actual finite étale algebra -/
@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open scoped TensorProduct
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [Module.Finite R A] [Algebra.Etale R A]

/-- At every original prime the actual finite étale algebra splits on a principal
neighborhood into a finite product of the same localized base. -/
theorem IsAbsolutelyIntegrallyClosed.finiteEtale_exists_principal_algEquiv
    (hR : IsAbsolutelyIntegrallyClosed R) (p : Ideal R) [p.IsPrime] :
    ∃ g : R, g ∉ p ∧ ∃ r : ℕ,
      Nonempty ((Localization.Away g) ⊗[R] A ≃ₐ[Localization.Away g]
        (Fin r → Localization.Away g)) := by
  letI : Module.FinitePresentation R A := Module.FinitePresentation.of_finite_of_finitePresentation R A
  obtain ⟨r, d, hd, ψ, e, hψ⟩ := hR.finiteEtale_exists_principal_comparison (A := A) p
  obtain ⟨g, hg, _hdg, E, _hE⟩ := principalAlgebraComparison_exists_algEquiv p d hd r ψ e hψ
  exact ⟨g, hg, r, ⟨E⟩⟩

/-- The original principal opens carrying an algebra splitting cover the whole base. -/
theorem IsAbsolutelyIntegrallyClosed.finiteEtale_principalSplitting_span_eq_top
    (hR : IsAbsolutelyIntegrallyClosed R) :
    Ideal.span {g : R | ∃ r : ℕ,
      Nonempty ((Localization.Away g) ⊗[R] A ≃ₐ[Localization.Away g]
        (Fin r → Localization.Away g))} = ⊤ := by
  by_contra hne
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
  letI := hm
  obtain ⟨g, hgm, r, e⟩ := hR.finiteEtale_exists_principal_algEquiv (A := A) m
  exact hgm (hle (Ideal.subset_span ⟨r, e⟩))

/-- One finite principal cover suffices, with an actual splitting on every member.
The ranks may vary between members; no constant-rank assumption is introduced. -/
theorem IsAbsolutelyIntegrallyClosed.finiteEtale_exists_finite_principal_cover
    (hR : IsAbsolutelyIntegrallyClosed R) :
    ∃ t : Finset R, Ideal.span (t : Set R) = ⊤ ∧
      ∀ g ∈ t, ∃ r : ℕ,
        Nonempty ((Localization.Away g) ⊗[R] A ≃ₐ[Localization.Away g]
          (Fin r → Localization.Away g)) := by
  classical
  let U : Set R := {g : R | ∃ r : ℕ,
    Nonempty ((Localization.Away g) ⊗[R] A ≃ₐ[Localization.Away g]
      (Fin r → Localization.Away g))}
  have hU : Ideal.span U = ⊤ := hR.finiteEtale_principalSplitting_span_eq_top (A := A)
  obtain ⟨t, htU, ht⟩ := (Ideal.span_eq_top_iff_finite U).mp hU
  exact ⟨t, ht, fun g hg => htU hg⟩

end SerrePositivity
