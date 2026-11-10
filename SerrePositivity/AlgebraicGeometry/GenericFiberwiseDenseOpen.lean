module

public import SerrePositivity.AlgebraicGeometry.GenericFreeAlgebra
public import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.Flat.Localization

/-!
概要：非零因子の主開は、基底を縮めるとどの底変換でも稠密になる。
方針：元による乗法の余核を一般自由性で平坦にし、底変換後の単射性を得る。
規約：基底を整域とし、始域の代数は有限型とする。
使われ方：生成ファイバーの幾何学的既約性を超曲面模型から移す。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open scoped TensorProduct nonZeroDivisors

/--
概要：整域上の有限型代数の非零因子は、基底のある非零元を反転した任意の底変換で非零因子。
方針：元による乗法の余核に一般自由性を適用する。
規約：底変換先は指定した基底の元が可逆になる任意の可換代数とする。
使われ方：アフィンチャートの主開のファイバーごとの稠密性。
-/
theorem exists_nonzero_forall_tensor_mem_nonZeroDivisors
    {A B : Type u} [CommRing A] [IsDomain A] [CommRing B] [Algebra A B]
    [Algebra.FiniteType A B] (b : B) (hb : b ∈ B⁰) :
    ∃ a : A, a ≠ 0 ∧ ∀ (C : Type v) [CommRing C] [Algebra A C],
      IsUnit (algebraMap A C a) → (1 ⊗ₜ[A] b : C ⊗[A] B) ∈ (C ⊗[A] B)⁰ := by
  let I : Ideal B := Ideal.span {b}
  let Q := B ⧸ I
  let f : B →ₗ[A] B := LinearMap.mulLeft A b
  let q : B →ₗ[A] Q := (Ideal.Quotient.mkₐ A I).toLinearMap
  have hf : Function.Injective f := by
    apply (LinearMap.ker_eq_bot).mp
    rw [LinearMap.ker_eq_bot']
    exact fun _ h => (mul_left_mem_nonZeroDivisors_eq_zero_iff hb).mp h
  have hq : Function.Surjective q := Ideal.Quotient.mk_surjective
  have hExact : Function.Exact f q := by
    intro x
    change Ideal.Quotient.mk I x = 0 ↔ ∃ y, b * y = x
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    exact exists_congr (fun _ => eq_comm)
  obtain ⟨a, ha, hfree⟩ := exists_nonzero_free_localization_of_finiteType A Q
  refine ⟨a, ha, ?_⟩
  intro C _ _ hu
  let S := Localization.Away a
  let j : S →+* C := IsLocalization.Away.lift a hu
  let : Algebra S C := j.toAlgebra
  let : IsScalarTower A S C :=
    IsScalarTower.of_algebraMap_eq fun x => (IsLocalization.Away.lift_eq a hu x).symm
  let : Module.Flat A S := IsLocalization.flat S (Submonoid.powers a)
  let : Module.Free S (S ⊗[A] Q) := hfree
  have hfS : Function.Injective (f.baseChange S) :=
    Module.Flat.lTensor_preserves_injective_linearMap f hf
  have hqS : Function.Surjective (q.baseChange S) := LinearMap.lTensor_surjective _ hq
  have hExactS : Function.Exact (f.baseChange S) (q.baseChange S) :=
    lTensor_exact _ hExact hq
  have hfSC : Function.Injective ((f.baseChange S).baseChange C) :=
    LinearMap.lTensor_injective_of_exact_of_flat _ hqS _ hfS hExactS C
  let e := TensorProduct.AlgebraTensorModule.cancelBaseChange A S C C B
  have hc : (f.baseChange C).comp e.toLinearMap =
      e.toLinearMap.comp ((f.baseChange S).baseChange C) :=
    TensorProduct.AlgebraTensorModule.lTensor_comp_cancelBaseChange A S C f
  have hfC : Function.Injective (f.baseChange C) := by
    intro x y h
    apply e.symm.injective
    apply hfSC
    apply e.injective
    change (e.toLinearMap.comp ((f.baseChange S).baseChange C)) (e.symm x) =
      (e.toLinearMap.comp ((f.baseChange S).baseChange C)) (e.symm y)
    rw [← hc]
    simpa using h
  have hMul : LinearMap.mulLeft C (1 ⊗ₜ[A] b : C ⊗[A] B) = f.baseChange C := by
    ext x
    simp [f, Algebra.TensorProduct.tmul_mul_tmul]
  refine mem_nonZeroDivisors_iff_left.mpr fun x hx => hfC ?_
  rw [← hMul]
  exact hx.trans (map_zero _).symm

/--
概要：非零因子を反転する主開は稠密。
方針：局所化の単射性から、局所化のスペクトルの像が稠密であると示す。
規約：環は可換とする。
使われ方：底変換後の非零因子からファイバー内の主開の稠密性を得る。
-/
theorem dense_basicOpen_of_mem_nonZeroDivisors {B : Type*} [CommRing B]
    {b : B} (hb : b ∈ B⁰) : Dense (PrimeSpectrum.basicOpen b : Set (PrimeSpectrum B)) := by
  let D := Localization.Away b
  have hpow : Submonoid.powers b ≤ B⁰ := by
    rintro _ ⟨n, rfl⟩
    exact pow_mem hb n
  have hInj : Function.Injective (algebraMap B D) := IsLocalization.injective D hpow
  rw [← PrimeSpectrum.localization_away_comap_range D b]
  exact (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr
    (((RingHom.injective_iff_ker_eq_bot _).mp hInj).le.trans bot_le)

end SerrePositivity.AlgebraicGeometry
