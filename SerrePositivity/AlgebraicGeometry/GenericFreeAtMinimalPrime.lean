module

public import SerrePositivity.AlgebraicGeometry.FinitePresentationNoetherianModel
public import SerrePositivity.AlgebraicGeometry.MinimalPrimeQuotientLocalization
public import SerrePositivity.AlgebraicGeometry.GenericFreeAlgebra

/-!
概要：被約な任意の基底の極小素点の近くで、有限表示代数が自由になる基本開を得る。
方針：係数の Noether 模型を整域商に移し、一般自由性の基本開を元の基底へ戻す。
規約：元の基底の Noether 性は仮定しない。自由階数の有限性も要求しない。
使われ方：Rydh 3.10 の準コンパクトな一般点集合を持つ基底の一般平坦性。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct
universe u

/-- 被約基底の各極小素点の近くで、有限表示代数が自由になる基本開がある。 -/
theorem exists_free_basicOpen_at_minimalPrime_of_finitePresentation
    (R B : Type u) [CommRing R] [IsReduced R] [CommRing B] [Algebra R B]
    [Algebra.FinitePresentation R B] {p : Ideal R} (hp : p ∈ minimalPrimes R) :
    ∃ r : R, r ∉ p ∧ Module.Free (Localization.Away r) (Localization.Away r ⊗[R] B) := by
  obtain ⟨R₀, _, _, _, B₀, _, _, _, hN, _, ⟨e⟩⟩ :=
    exists_finitePresentation_noetherian_model R B
  let f : R₀ →+* R := algebraMap R₀ R
  let J := p.comap f
  have : p.IsPrime := hp.1.1
  have : J.IsPrime := Ideal.IsPrime.comap f
  let Q := R₀ ⧸ J
  let C := Q ⊗[R₀] B₀
  obtain ⟨t, ht, hfree⟩ := exists_nonzero_free_localization_of_finiteType Q C
  obtain ⟨r, hr, l, hl⟩ := exists_away_quotient_localization_factor_of_minimalPrime
    f hp J.fg_of_isNoetherianRing t ht
  let D := Localization.Away r
  let L := Localization.Away t
  let : Algebra R₀ D := inferInstance
  let : Algebra R₀ L := inferInstance
  let : Algebra L D := l.toAlgebra
  let : Algebra Q D := (l.comp (algebraMap Q L)).toAlgebra
  have : IsScalarTower R₀ R D := inferInstance
  have : IsScalarTower R₀ Q L := inferInstance
  have : IsScalarTower Q L D := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower R₀ L D := IsScalarTower.of_algebraMap_eq fun a ↦
    (RingHom.congr_fun hl a).symm
  have : IsScalarTower R₀ Q D := IsScalarTower.of_algebraMap_eq fun a ↦
    (RingHom.congr_fun hl a).symm
  let : Module.Free L (L ⊗[Q] C) := hfree
  let : Module.Free D (D ⊗[L] (L ⊗[Q] C)) := inferInstance
  let : Module.Free D (D ⊗[Q] C) := Module.Free.of_equiv
    (Algebra.TensorProduct.cancelBaseChange Q L D D C).toLinearEquiv
  let : Module.Free D (D ⊗[R₀] B₀) := Module.Free.of_equiv
    (Algebra.TensorProduct.cancelBaseChange R₀ Q D D B₀).toLinearEquiv
  let e₁ := (Algebra.TensorProduct.cancelBaseChange R₀ R D D B₀).symm
  let e₂ := Algebra.TensorProduct.congr (AlgEquiv.refl : D ≃ₐ[D] D) e
  exact ⟨r, hr, Module.Free.of_equiv (e₁.trans e₂).toLinearEquiv⟩

end SerrePositivity.AlgebraicGeometry
