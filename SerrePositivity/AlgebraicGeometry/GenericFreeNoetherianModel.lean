module

public import SerrePositivity.AlgebraicGeometry.GenericFlatCommonCoefficients
public import SerrePositivity.AlgebraicGeometry.FinitePresentationNoetherianModel

/-!
概要：有限表示代数の Noether 模型に、一般自由な有限個の基本開を添える。
方針：共通係数部分代数へ元の模型を底変換し、実際の tensor 同型を合成する。
規約：元の基底の Noether 性は要求しない。選んだ開は全極小素点を覆う。
使われ方：Rydh 3.7 の指定平坦開を伴う Noether 模型への接続。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct
universe u

/-- 有限表示代数は、全極小素点を覆う一般自由開を伴う Noether 模型の実際の底変換。 -/
theorem exists_generic_free_noetherian_model
    (R B : Type u) [CommRing R] [IsReduced R] [CommRing B] [Algebra R B]
    [Algebra.FinitePresentation R B]
    (hmin : IsCompact {q : PrimeSpectrum R | q.asIdeal ∈ minimalPrimes R}) :
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra ℤ A) (_ : Algebra A R)
      (S : Type u) (_ : CommRing S) (_ : Algebra A S),
      Algebra.FiniteType ℤ A ∧ IsNoetherianRing A ∧ Algebra.FinitePresentation A S ∧
        Nonempty (R ⊗[A] S ≃ₐ[R] B) ∧ ∃ (n : ℕ) (t : Fin n → A),
          (∀ i, Module.Free (Localization.Away (t i)) (Localization.Away (t i) ⊗[A] S)) ∧
          ∀ q : PrimeSpectrum R, q.asIdeal ∈ minimalPrimes R →
            ∃ i, algebraMap A R (t i) ∉ q.asIdeal := by
  obtain ⟨A₀, _, _, _, S₀, _, _, hA₀, hN₀, hS₀, ⟨e⟩⟩ :=
    exists_finitePresentation_noetherian_model R B
  letI : Algebra.FiniteType ℤ A₀ := hA₀
  letI : IsNoetherianRing A₀ := hN₀
  letI : Algebra.FinitePresentation A₀ S₀ := hS₀
  obtain ⟨T, hT, n, t, hfree, hcover⟩ :=
    exists_common_fg_subalgebra_generic_free_charts A₀ R S₀ hmin
  letI : Algebra.FiniteType A₀ T := (Subalgebra.fg_iff_finiteType T).mp hT
  letI := IsScalarTower.of_algebraMap_eq' (R := ℤ) (S := A₀) (A := T)
    (Subsingleton.elim _ _)
  have hTℤ : Algebra.FiniteType ℤ T := Algebra.FiniteType.trans hA₀ inferInstance
  have hNT : IsNoetherianRing T := isNoetherianRing_of_fg hT
  let S := T ⊗[A₀] S₀
  have hS : Algebra.FinitePresentation T S := inferInstance
  let e' : R ⊗[T] S ≃ₐ[R] B :=
    (Algebra.TensorProduct.cancelBaseChange A₀ T R R S₀).trans e
  refine ⟨T, inferInstance, inferInstance, inferInstance, S, inferInstance,
    inferInstance, hTℤ, hNT, hS, ⟨e'⟩, n, t, ?_, hcover⟩
  intro i
  let D := Localization.Away (t i)
  letI : Module.Free D (D ⊗[A₀] S₀) := hfree i
  exact Module.Free.of_equiv
    (Algebra.TensorProduct.cancelBaseChange A₀ T D D S₀).symm.toLinearEquiv

end SerrePositivity.AlgebraicGeometry
