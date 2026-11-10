module

public import SerrePositivity.AlgebraicGeometry.GenericFiberwiseDenseOpen
import Mathlib.Algebra.Ring.Hom.InjSurj
import Mathlib.RingTheory.Localization.BaseChange

/-!
概要：共通の主開を持つ有限型アフィン代数の幾何学的整性を、稠密開上で比較する。
方針：二つの主開が各ファイバーで非零因子を反転するように基底を縮める。
規約：基底は整域とし、共通の主開は基底上の代数同型で与える。
使われ方：変数の宇宙に依存せず、超曲面模型の幾何学的整性を移す。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open scoped TensorProduct nonZeroDivisors

/--
概要：共通の主開を持つ二つの有限型代数の一方が稠密主開上で幾何学的に整なら、他方も稠密主開上で整。
方針：非零因子の主開の同型を底変換し、局所化への単射を使う。
規約：共通の主開は両側で非零因子の反転により与える。
使われ方：滑らかな族と超曲面模型のファイバーを比較する。
-/
theorem exists_nonzero_forall_isDomain_tensor_of_common_away
    {A B C : Type u} [CommRing A] [IsDomain A]
    [CommRing B] [Algebra A B] [Algebra.FiniteType A B]
    [CommRing C] [Algebra A C] [Algebra.FiniteType A C]
    (a : A) (ha : a ≠ 0)
    (hModel : ∀ (F : Type v) [Field F] [Algebra A F], algebraMap A F a ≠ 0 →
      IsDomain (F ⊗[A] C))
    {b : B} (hb : b ∈ B⁰) {c : C} (hc : c ∈ C⁰)
    (e : Localization.Away b ≃ₐ[A] Localization.Away c) :
    ∃ t : A, t ≠ 0 ∧ ∀ (F : Type v) [Field F] [Algebra A F], algebraMap A F t ≠ 0 →
      IsDomain (F ⊗[A] B) := by
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
