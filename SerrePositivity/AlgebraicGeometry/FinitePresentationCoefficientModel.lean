module

public import SerrePositivity.AlgebraicGeometry.FinitePresentationNoetherianModel

/-!
概要：有限表示の affine 模型を、指定した Noether 係数環の上で取る。
方針：有限個の関係式の係数を k-部分代数へ入れ、Mathlib の tensor 模型を使う。
規約：k=F_p のときも係数体を保持する。元の環 R の Noether 性は要求しない。
使われ方：G2 の有限型 F_p の模型の affine 局所。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct
universe u v

/-- 指定した Noether 係数環の上で、有限表示代数の affine 模型を取れる。 -/
theorem exists_finitePresentation_model_over_noetherian_coefficients
    (k : Type v) (R S : Type u) [CommRing k] [IsNoetherianRing k]
    [CommRing R] [Algebra k R] [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S] :
    ∃ A : Subalgebra k R,
      A.FG ∧ IsNoetherianRing A ∧ ∃ (S₀ : Type u) (_ : CommRing S₀) (_ : Algebra A S₀),
        Algebra.FinitePresentation A S₀ ∧ Nonempty (R ⊗[A] S₀ ≃ₐ[R] S) := by
  let P := Algebra.Presentation.ofFinitePresentation R S
  let A := Algebra.adjoin k P.coeffs
  have hA : A.FG := Subalgebra.fg_def.mpr ⟨P.coeffs, P.finite_coeffs, rfl⟩
  letI : P.HasCoeffs A := ⟨by
    intro r hr
    exact ⟨⟨r, Algebra.subset_adjoin hr⟩, rfl⟩⟩
  refine ⟨A, hA, isNoetherianRing_of_fg hA,
    P.ModelOfHasCoeffs A, inferInstance, inferInstance, inferInstance, ?_⟩
  exact ⟨P.tensorModelOfHasCoeffsEquiv A⟩

end SerrePositivity.AlgebraicGeometry
