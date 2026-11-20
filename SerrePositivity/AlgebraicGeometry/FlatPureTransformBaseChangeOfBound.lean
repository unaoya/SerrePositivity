module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.BoundaryPowerLift
public import SerrePositivity.AlgebraicGeometry.ScalarInverseBaseChange
public import SerrePositivity.AlgebraicGeometry.PureTransformImage
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
概要：KST §5、Stacks 0815, Theorem 38.30.7 の純変換の追加基底変更を境界ねじれの一様性だけで比較する。
方針：境界ねじれを消す冪から戻し写像を作り、基底変更後の核を同定する。
規約：基礎環上の有限生成性や Noether 性は不要。
使われ方：有限型代数上の有限加群の純変換にも安定性を適用する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct

variable {R : Type*} [CommRing R] (C : Type*) [CommRing C] [Algebra R C]
  (f : R) (M : Type*) [AddCommGroup M] [Module R M]
  [Module.Flat R (modulePureTransform f M)]

/--
概要：境界ねじれが一様な冪で消えれば、追加基底変更の純変換は元の平坦な商の基底変更と同型。
方針：商写像の冪倍の戻し写像を基底変更し、像との同型を使う。
規約：KST §5、Stacks 0815, Theorem 38.30.7、追加係数環で境界元の像は正則。
使われ方：基礎環上有限ではない加群の共通細分での平坦性保存。
-/
def flatPureTransformBaseChangeEquivOfBound (n : ℕ)
    (hn : ∀ m ∈ boundaryTorsion f M, f ^ n • m = 0)
    (hf : IsRegular (algebraMap R C f)) :
    modulePureTransform (algebraMap R C f) (C ⊗[R] M) ≃ₗ[C]
      C ⊗[R] modulePureTransform f M := by
  let q := (boundaryTorsion f M).mkQ
  let h := boundaryPowerLift f M n hn
  have hh : h.comp q = f ^ n • LinearMap.id := boundaryPowerLift_comp_mkQ f M n hn
  have hreg : IsSMulRegular (C ⊗[R] modulePureTransform f M) (algebraMap R C f) :=
    Module.Flat.isSMulRegular_of_isRegular hf
  let e := modulePureTransformEquivImage (algebraMap R C f) (q.baseChange C) hreg
    (fun z hz => ⟨n, by
      rw [← map_pow]
      exact baseChange_ker_annihilated_of_scalar_leftInverse q h (f ^ n) hh z hz⟩)
  have hsurj : Function.Surjective (q.baseChange C) :=
    LinearMap.baseChange_surjective C (boundaryTorsion f M).mkQ_surjective
  exact e.trans (LinearEquiv.ofTop _ (LinearMap.range_eq_top.mpr hsurj))

/--
概要：一様に消える境界ねじれを持つ平坦な純変換は追加基底変更後にも平坦。
方針：元の平坦な商の基底変更との実際の同型を使う。
規約：KST §5、Stacks 0815, Theorem 38.30.7、元の加群の基礎環上の有限性は不要。
使われ方：有限型代数上の有限加群の純変換の安定性。
-/
theorem flatPureTransform_baseChange_of_bound (n : ℕ)
    (hn : ∀ m ∈ boundaryTorsion f M, f ^ n • m = 0)
    (hf : IsRegular (algebraMap R C f)) :
    Module.Flat C (modulePureTransform (algebraMap R C f) (C ⊗[R] M)) :=
  Module.Flat.of_linearEquiv (flatPureTransformBaseChangeEquivOfBound C f M n hn hf)

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
