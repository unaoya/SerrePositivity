module

public import SerrePositivity.AlgebraicGeometry.GenericHigherMinorVanishing
public import SerrePositivity.AlgebraicGeometry.GenericMinorCoefficientCenter

/-!
概要：KST §5、Stacks 0810 の一定一般階数の下での小行列式の係数イデアルの単位性。
方針：全拡大素点での小行列式の単位性を係数イデアルへ移す。
規約：元の代数の実際の分裂表示と完全な有限関係式表示を使う。
使われ方：境界で局所化した後の単位性から admissible 中心の境界冪を得る。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry
open scoped TensorProduct

/--
概要：相対平坦な有限加群の一定一般階数に対応する小行列式の係数イデアルは単位。
方針：各拡大素点での自由階数を小行列式の非包含へ移し、係数の境界冪判定を単位元に使う。
規約：KST §5、Stacks 0810, Lemma 38.30.2、有限表示性は Noether 性から導く。
使われ方：境界外での係数イデアルの単位性を証明する。
-/
theorem minorCoefficientIdeal_eq_top_of_constant_genericRank
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [Module.Flat A B] [Algebra.FinitePresentation A B]
    [GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap A B)))]
    {M ι m n : Type*} [AddCommGroup M] [Module A M] [Module B M]
    [IsScalarTower A B M] [Module.Flat A M] [Module.Finite B M] [Fintype m] [Finite n]
    (e : B →ₗ[A] (ι →₀ A)) (p : (ι →₀ A) →ₗ[A] B) (hpe : p.comp e = LinearMap.id)
    (q : (m → B) →ₗ[B] M) (hq : Function.Surjective q) (H : Matrix m n B)
    (hH : Submodule.span B (Set.range H.col) = LinearMap.ker q) (r : ℕ)
    (hrank : ∀ P : PrimeSpectrum A,
      let L := Localization.AtPrime (geometricallyIntegralGenericPrime A B P).asIdeal
      Module.finrank L (L ⊗[B] M) = r) :
    splitAlgebraCoefficientIdeal e (matrixMinorIdeal H (Fintype.card m - r)) = ⊤ := by
  classical
  let : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  let : Module.FinitePresentation B M := Module.finitePresentation_of_finite B M
  let J := matrixMinorIdeal H (Fintype.card m - r)
  have hJ : ∀ P : Ideal A, P.IsPrime → (1 : A) ∉ P →
      ¬ J ≤ P.map (algebraMap A B) := by
    intro P hP _
    let : P.IsPrime := hP
    let : (P.map (algebraMap A B)).IsPrime := ideal_map_isPrime_of_geometricallyIntegral A B P
    let L := Localization.AtPrime (P.map (algebraMap A B))
    let : Module.Free L (L ⊗[B] M) := free_at_geometricallyIntegralGenericPrime A B ⟨P, hP⟩
    have hr : Module.finrank L (L ⊗[B] M) = r := hrank ⟨P, hP⟩
    have hpat := minorIdeal_images_at_tensor_finrank (C := L) H q hq hH
    have hunit : J.map (algebraMap B L) = ⊤ := by
      simpa only [hr] using hpat.1
    exact not_le_prime_of_atPrime_map_eq_top (P.map (algebraMap A B)) J hunit
  obtain ⟨N, hN⟩ := exists_pow_mem_splitAlgebraCoefficientIdeal e p hpe J 1 hJ
  apply (Ideal.eq_top_iff_one _).mpr
  simpa only [one_pow] using hN

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
