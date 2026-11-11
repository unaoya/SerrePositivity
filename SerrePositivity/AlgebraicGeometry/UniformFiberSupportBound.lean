module

public import SerrePositivity.AlgebraicGeometry.FiberSupportNormalization
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-!
概要：有限型代数上の有限加群では、全ファイバーの台の次元を同じ自然数で抑えられる。
方針：零化イデアルによる商の有限個の生成元を、任意の剰余体へ移す。
規約：台が空のファイバーも含める。
使われ方：Stacks 0815 のファイバー台の次元帰納を開始する。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open scoped TensorProduct

/--
概要：有限型代数の全剰余体ファイバーの Krull 次元は、同じ有限の上限を持つ。
方針：多項式環からの全射を全ファイバーへ底変換し、多項式環の次元を使う。
規約：ファイバー環は剰余体を左因子にする。
使われ方：有限加群の台の次元の一様な上限。
-/
theorem exists_uniform_ringKrullDim_fiber_bound
    (R B : Type*) [CommRing R] [CommRing B] [Algebra R B] [Algebra.FiniteType R B] :
    ∃ n : ℕ, ∀ p : PrimeSpectrum R, ringKrullDim (p.asIdeal.Fiber B) ≤ n := by
  obtain ⟨n, f, hf⟩ := (Algebra.FiniteType.iff_quotient_mvPolynomial'' (R := R) (S := B)).mp
    inferInstance
  refine ⟨n, fun p => ?_⟩
  let K := p.asIdeal.ResidueField
  let P := MvPolynomial (Fin n) R
  let g := Algebra.TensorProduct.map (AlgHom.id R K) f
  have hg : Function.Surjective g :=
    LinearMap.lTensor_surjective K hf
  calc
    ringKrullDim (p.asIdeal.Fiber B) ≤ ringKrullDim (K ⊗[R] P) :=
      ringKrullDim_le_of_surjective g.toRingHom hg
    _ = n := by
      rw [ringKrullDim_eq_of_ringEquiv (MvPolynomial.algebraTensorAlgEquiv R K).toRingEquiv]
      simp [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
        ringKrullDim_eq_zero_of_field]

/--
概要：有限型代数上の有限加群の各剰余体ファイバーで、台の次元に一を足した値は一様な自然数以下。
方針：零化イデアルで切り出した台を有限型代数のファイバー次元の評価に渡す。
規約：基礎環の Noether 性は要求しない。
使われ方：台の次元に関する自然数帰納の入力を得る。
-/
theorem exists_uniform_supportDim_fiber_bound
    {R B M : Type*} [CommRing R] [CommRing B] [Algebra R B] [Algebra.FiniteType R B]
    [AddCommGroup M] [Module B M] [Module.Finite B M] :
    ∃ n : ℕ, ∀ p : PrimeSpectrum R, let D := B ⊗[R] p.asIdeal.ResidueField
      Module.supportDim D (D ⊗[B] M) + 1 ≤ (n : WithBot ℕ∞) := by
  let E := B ⧸ Module.annihilator B M
  have : Algebra.FiniteType R E :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ R _) Ideal.Quotient.mk_surjective
  obtain ⟨n, hn⟩ := exists_uniform_ringKrullDim_fiber_bound R E
  refine ⟨n + 1, fun p => ?_⟩
  dsimp only
  rw [supportDim_baseChange_eq_ringKrullDim_quotientAnnihilator]
  change ringKrullDim (p.asIdeal.Fiber E) + 1 ≤ ((n + 1 : ℕ) : WithBot ℕ∞)
  rw [Nat.cast_add, Nat.cast_one]
  exact add_le_add (hn p) le_rfl

end SerrePositivity.AlgebraicGeometry
