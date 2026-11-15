module

public import SerrePositivity.AlgebraicGeometry.FinitePresentationCoefficientModel

/-!
概要：有限個の有限表示代数の affine 模型を、同じ係数部分代数上へそろえる。
方針：有限個の関係式の係数集合の和集合を取り、同じ tensor 模型を使う。
規約：元の環の Noether 性は要求しない。係数環 k を保つ。
使われ方：G2 の有限アフィン被覆の模型の共通係数。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct
universe u v w

/-- 有限個の有限表示代数の模型を、一つの有限生成係数部分代数上で取れる。 -/
theorem exists_common_finitePresentation_coefficient_models
    (k : Type v) (R : Type u) [CommRing k] [IsNoetherianRing k] [CommRing R] [Algebra k R]
    {ι : Type w} [Finite ι] (S : ι → Type u) [∀ i, CommRing (S i)]
    [∀ i, Algebra R (S i)] [∀ i, Algebra.FinitePresentation R (S i)] :
    ∃ A : Subalgebra k R, A.FG ∧ IsNoetherianRing A ∧
      ∀ i, ∃ (S₀ : Type u) (_ : CommRing S₀) (_ : Algebra A S₀),
        Algebra.FinitePresentation A S₀ ∧ Nonempty (R ⊗[A] S₀ ≃ₐ[R] S i) := by
  let P (i : ι) := Algebra.Presentation.ofFinitePresentation R (S i)
  let c : Set R := ⋃ i, (P i).coeffs
  have hc : c.Finite := Set.finite_iUnion (fun i ↦ (P i).finite_coeffs)
  let A := Algebra.adjoin k c
  have hA : A.FG := Subalgebra.fg_def.mpr ⟨c, hc, rfl⟩
  refine ⟨A, hA, isNoetherianRing_of_fg hA, ?_⟩
  intro i
  letI : (P i).HasCoeffs A := ⟨by
    intro r hr
    exact ⟨⟨r, Algebra.subset_adjoin (Set.mem_iUnion.mpr ⟨i, hr⟩)⟩, rfl⟩⟩
  exact ⟨(P i).ModelOfHasCoeffs A, inferInstance, inferInstance,
    inferInstance, ⟨(P i).tensorModelOfHasCoeffsEquiv A⟩⟩

end SerrePositivity.AlgebraicGeometry
