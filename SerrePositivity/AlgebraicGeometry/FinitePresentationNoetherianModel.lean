module

public import Mathlib.RingTheory.Extension.Presentation.Core
public import Mathlib.RingTheory.Adjoin.FG

/-!
概要：有限表示代数を、係数が生成する Noether 環の上の模型から実際に復元する。
方針：Mathlib の有限表示の Core と、その上の ModelOfHasCoeffs を再利用する。
規約：模型との比較はテンソル積の代数同型。元の基底への忠実平坦性は要求しない。
使われ方：非 Noether 基底での一般平坦性と、有限表示スキームの近似のアフィン局所。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct
universe u

/-- 有限表示代数は、ℤ 上有限型の Noether 環上の有限表示代数の底変換。 -/
theorem exists_finitePresentation_noetherian_model
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S] :
    ∃ (R₀ : Type u) (_ : CommRing R₀) (_ : Algebra ℤ R₀) (_ : Algebra R₀ R)
      (S₀ : Type u) (_ : CommRing S₀) (_ : Algebra R₀ S₀),
      Algebra.FiniteType ℤ R₀ ∧ IsNoetherianRing R₀ ∧
        Algebra.FinitePresentation R₀ S₀ ∧ Nonempty (R ⊗[R₀] S₀ ≃ₐ[R] S) := by
  let P := Algebra.Presentation.ofFinitePresentation R S
  have hN : IsNoetherianRing P.Core := by
    change IsNoetherianRing P.core
    exact isNoetherianRing_of_fg (Subalgebra.fg_def.mpr ⟨P.coeffs, P.finite_coeffs, rfl⟩)
  refine ⟨P.Core, inferInstance, inferInstance, inferInstance,
    P.ModelOfHasCoeffs P.Core, inferInstance, inferInstance,
    inferInstance, hN, inferInstance, ?_⟩
  exact ⟨P.tensorModelOfHasCoeffsEquiv P.Core⟩

end SerrePositivity.AlgebraicGeometry
