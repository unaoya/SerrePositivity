module

public import SerrePositivity.AlgebraicGeometry.FlatPureTransformBaseChangeOfBound
public import SerrePositivity.AlgebraicGeometry.BoundaryPowerLift
public import SerrePositivity.AlgebraicGeometry.ScalarInverseBaseChange
public import SerrePositivity.AlgebraicGeometry.PureTransformImage
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
概要：KST §5、Stacks 0815 の平坦な純変換の追加の基底変更に対する安定性。
方針：一様に消えるねじれから冪倍の戻し写像を作り、基底変更後の核を境界ねじれと同定する。
規約：境界元の像が追加した係数環で正則であることを仮定する。
使われ方：admissible blowup の共通細分で局所平坦化を保存する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct

variable {R : Type*} [CommRing R] (C : Type*) [CommRing C] [Algebra R C]
  (f : R) (M : Type*) [AddCommGroup M] [Module R M]
  [IsNoetherianRing R] [Module.Finite R M] [Module.Flat R (modulePureTransform f M)]

/--
概要：追加の基底変更の純変換と、元の平坦な純変換の基底変更の実際の線形同型。
方針：商写像の基底変更の全射性と、その核の冪消滅・標的の正則作用を使う。
規約：KST §5、Stacks 0815、元の加群は Noether 環上有限。
使われ方：平坦化したチャートをさらに細分したときの純変換の同定。
-/
def flatPureTransformBaseChangeEquiv (hf : IsRegular (algebraMap R C f)) :
    modulePureTransform (algebraMap R C f) (C ⊗[R] M) ≃ₗ[C]
      C ⊗[R] modulePureTransform f M := by
  let n := Classical.choose (exists_pow_annihilates_boundaryTorsion_of_noetherian f M)
  have hn := Classical.choose_spec (exists_pow_annihilates_boundaryTorsion_of_noetherian f M)
  exact flatPureTransformBaseChangeEquivOfBound C f M n hn hf

/--
概要：平坦な純変換は正則な境界を保つ任意の追加基底変更後にも平坦。
方針：元の純変換の基底変更との実際の同型で平坦性を移す。
規約：KST §5、Stacks 0815、追加の基底変更自体の平坦性は不要。
使われ方：admissible な blowup の共通細分後の平坦性の保存。
-/
theorem flatPureTransform_baseChange (hf : IsRegular (algebraMap R C f)) :
    Module.Flat C (modulePureTransform (algebraMap R C f) (C ⊗[R] M)) :=
  Module.Flat.of_linearEquiv (flatPureTransformBaseChangeEquiv C f M hf)

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
