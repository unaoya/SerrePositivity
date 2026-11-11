module

public import SerrePositivity.AlgebraicGeometry.GenericFiberwiseDenseOpen
public import SerrePositivity.AlgebraicGeometry.HypersurfaceGeometricFiber
import Mathlib.RingTheory.Localization.BaseChange

/-!
概要：超曲面模型との共通の主開から、幾何学的整なファイバーを元のアフィン代数へ移す。
方針：各ファイバーで二つの主開を比較し、非零因子の局所化への単射を使う。
規約：共通の主開は基底上で同型な非零因子の局所化として与える。
使われ方：滑らかな族の幾何学的連結な生成ファイバーを基底の稠密開上に広げる。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open scoped TensorProduct nonZeroDivisors

/--
概要：絶対既約な生成方程式を持つ超曲面と共通の主開を持つ有限型代数は、
基底のある主開上の任意の体への底変換で整域になる。
方針：一般自由性で主開を定める元の非零因子性を保ち、主開の同型を底変換する。
規約：両側の主開を定める元は非零因子とする。
使われ方：Stacks 0559 の双有理な模型から元のアフィンへの移行。
-/
theorem exists_nonzero_forall_isDomain_tensor_of_away_equiv_hypersurface
    {A B σ : Type u} {K : Type v} [CommRing A] [IsDomain A]
    [CommRing B] [Algebra A B] [Algebra.FiniteType A B]
    [Field K] [Algebra A K] [IsFractionRing A K] [Finite σ]
    (P : MvPolynomial σ A)
    (hP : Irreducible (MvPolynomial.map (algebraMap A (AlgebraicClosure K)) P))
    {b : B} (hb : b ∈ B⁰) {c : MvPolynomial σ A ⧸ Ideal.span {P}}
    (hc : c ∈ (MvPolynomial σ A ⧸ Ideal.span {P})⁰)
    (e : Localization.Away b ≃ₐ[A] Localization.Away c) :
    ∃ a : A, a ≠ 0 ∧ ∀ (F : Type w) [Field F] [Algebra A F], algebraMap A F a ≠ 0 →
      IsDomain (F ⊗[A] B) := by
  let C := MvPolynomial σ A ⧸ Ideal.span {P}
  obtain ⟨a, ha, hModel⟩ := exists_nonzero_forall_isDomain_tensor_hypersurface P hP
  obtain ⟨r, hr, hB⟩ := exists_nonzero_forall_tensor_mem_nonZeroDivisors (A := A) b hb
  obtain ⟨s, hs, hC⟩ := exists_nonzero_forall_tensor_mem_nonZeroDivisors (A := A) c hc
  refine ⟨a * (r * s), mul_ne_zero ha (mul_ne_zero hr hs), ?_⟩
  intro F _ _ hOpen
  rw [map_mul, map_mul, mul_ne_zero_iff, mul_ne_zero_iff] at hOpen
  let : IsDomain (F ⊗[A] C) := hModel F hOpen.1
  let bF : F ⊗[A] B := 1 ⊗ₜ[A] b
  let cF : F ⊗[A] C := 1 ⊗ₜ[A] c
  have hbF : bF ∈ (F ⊗[A] B)⁰ := hB F (isUnit_iff_ne_zero.mpr hOpen.2.1)
  have hcF : cF ≠ 0 :=
    mem_nonZeroDivisors_iff_ne_zero.mp (hC F (isUnit_iff_ne_zero.mpr hOpen.2.2))
  let : IsDomain (Localization.Away cF) := Localization.Away.isDomain hcF
  let eB := IsLocalization.Away.tensorProductEquivTMulRight A F b (Localization.Away b)
  let eC := IsLocalization.Away.tensorProductEquivTMulRight A F c (Localization.Away c)
  let eF : Localization.Away bF ≃ₐ[F] Localization.Away cF :=
    eB.symm.trans ((Algebra.TensorProduct.congr (AlgEquiv.refl : F ≃ₐ[F] F) e).trans eC)
  let : IsDomain (Localization.Away bF) :=
    Function.Injective.isDomain eF.toRingHom eF.injective
  have hPowers : Submonoid.powers bF ≤ (F ⊗[A] B)⁰ := by
    rintro _ ⟨n, rfl⟩
    exact pow_mem hbF n
  exact Function.Injective.isDomain (algebraMap _ (Localization.Away bF))
    (IsLocalization.injective _ hPowers)

end SerrePositivity.AlgebraicGeometry
