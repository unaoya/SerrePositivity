module

public import SerrePositivity.AlgebraicGeometry.FlatPureTransformBaseChangeOfBound
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-!
概要：純変換の平坦性を忠実平坦な底変換に沿って降ろす。
方針：平坦な底変換は純変換上の境界元の作用の単射性を保つので、純変換と底変換を交換する。
規約：境界ねじれを一様に消す冪を入力する。
使われ方：共通中心へ引き戻した étale 局所の純変換から、元の純変換を平坦にする。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open scoped TensorProduct

/--
概要：平坦な係数変更後の純変換は、元の純変換の係数変更と同型。
方針：境界元の作用の単射性を平坦性で保ち、商写像の核は境界元の冪で消えることを使う。
規約：元の純変換に平坦性を仮定せず、境界ねじれを一様に消す冪を仮定する。
使われ方：純変換の平坦性を忠実平坦な底変換で反映する。
-/
def pureTransformFlatCoefficientChangeEquivOfBound
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
    [AddCommGroup M] [Module R M] (a : R) (n : ℕ)
    (hn : ∀ m ∈ boundaryTorsion a M, a ^ n • m = 0) :
    modulePureTransform (algebraMap R S a) (S ⊗[R] M) ≃ₗ[S]
      S ⊗[R] modulePureTransform a M := by
  let Q := modulePureTransform a M
  let q := (boundaryTorsion a M).mkQ
  let h := boundaryPowerLift a M n hn
  have hh : h.comp q = a ^ n • LinearMap.id := boundaryPowerLift_comp_mkQ a M n hn
  have hreg : IsSMulRegular (S ⊗[R] Q) (algebraMap R S a) := by
    have hinj : Function.Injective ((a • (LinearMap.id : Q →ₗ[R] Q)).baseChange S) :=
      Module.Flat.lTensor_preserves_injective_linearMap
        (a • (LinearMap.id : Q →ₗ[R] Q)) (modulePureTransform_isSMulRegular a M)
    rw [LinearMap.baseChange_smul, LinearMap.baseChange_id] at hinj
    intro x y hxy
    apply hinj
    simpa only [LinearMap.smul_apply, LinearMap.id_apply, IsScalarTower.algebraMap_smul] using hxy
  let e := modulePureTransformEquivImage (algebraMap R S a) (q.baseChange S) hreg
    (fun z hz => ⟨n, by
      rw [← map_pow]
      exact baseChange_ker_annihilated_of_scalar_leftInverse q h (a ^ n) hh z hz⟩)
  have hq : Function.Surjective (q.baseChange S) :=
    LinearMap.baseChange_surjective S (boundaryTorsion a M).mkQ_surjective
  exact e.trans (LinearEquiv.ofTop _ (LinearMap.range_eq_top.mpr hq))

/--
概要：忠実平坦な底変換の先で純変換が平坦なら、元の純変換も平坦。
方針：純変換と平坦底変換の比較同型を、加群の平坦性の忠実平坦降下に渡す。
規約：境界ねじれは一様な冪で消えるものとする。
使われ方：Stacks 0814 の共通中心で、étale 局所から平坦性を降下する。
-/
theorem modulePureTransform_flat_of_faithfullyFlat_of_bound
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.FaithfullyFlat R S]
    [AddCommGroup M] [Module R M] (a : R) (n : ℕ)
    (hn : ∀ m ∈ boundaryTorsion a M, a ^ n • m = 0)
    [Module.Flat S (modulePureTransform (algebraMap R S a) (S ⊗[R] M))] :
    Module.Flat R (modulePureTransform a M) := by
  let : Module.Flat S (S ⊗[R] modulePureTransform a M) :=
    Module.Flat.of_linearEquiv (pureTransformFlatCoefficientChangeEquivOfBound a n hn).symm
  exact Module.Flat.of_flat_tensorProduct R (modulePureTransform a M) S

end SerrePositivity.AlgebraicGeometry
