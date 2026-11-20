module

public import SerrePositivity.AlgebraicGeometry.IdealPureTransform
public import SerrePositivity.AlgebraicGeometry.ChartBoundaryRegular
public import SerrePositivity.AlgebraicGeometry.Cartier
public import SerrePositivity.AlgebraicGeometry.BlowupAway

/-!
概要：KST §5、Stacks 0815 の平坦化をイデアル加群の場合に構成する。
方針：純変換を拡大イデアルと同定し、例外イデアルの実際の自由化を使う。
規約：正則な境界元の一つの冪が中心イデアルに入ると仮定する。
使われ方：一般の加群の平坦化に先立つ具体的な特殊形。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct

variable {R : Type*} [CommRing R] (I : Ideal R) (a : I)
  (f : R) (n : ℕ) (hn : f ^ n ∈ I) (hf : f ∈ nonZeroDivisors R)

include hn hf

/--
概要：イデアル加群のチャート上の純変換は係数環と線形同型。
方針：乗法写像の核を境界ねじれと同定し、正則単項イデアルの自由化と合成する。
規約：KST §5、Stacks 0815、基底変更の代数構造はチャートの係数写像。
使われ方：イデアル加群の純変換の実際の平坦化。
-/
def chartIdealPureTransformEquiv :
    letI : Algebra R (BlowupChartRing I a) := (chartBaseMap I a).toAlgebra
    modulePureTransform (chartBaseMap I a f) (BlowupChartRing I a ⊗[R] I) ≃ₗ[
      BlowupChartRing I a] BlowupChartRing I a := by
  letI : Algebra R (BlowupChartRing I a) := (chartBaseMap I a).toAlgebra
  have hreg : IsRegular (algebraMap R (BlowupChartRing I a) f) :=
    isRegular_iff_mem_nonZeroDivisors.mpr (chartBaseMap_nonZeroDivisors I a hf)
  exact (idealPureTransformEquiv I f n hn hreg).trans (chartExceptionalIdealEquiv I a).symm

/--
概要：イデアル加群のチャート上の純変換は平坦。
方針：係数環との実際の線形同型で平坦性を移送する。
規約：KST §5、Stacks 0815、一般の有限型代数上の有限加群の結論とは区別する。
使われ方：blowup によるイデアル加群の平坦化の特殊例。
-/
theorem chartIdealPureTransform_flat :
    let : Algebra R (BlowupChartRing I a) := (chartBaseMap I a).toAlgebra
    Module.Flat (BlowupChartRing I a)
      (modulePureTransform (chartBaseMap I a f) (BlowupChartRing I a ⊗[R] I)) := by
  let : Algebra R (BlowupChartRing I a) := (chartBaseMap I a).toAlgebra
  exact Module.Flat.of_linearEquiv (chartIdealPureTransformEquiv I a f n hn hf)

omit hf in
/--
概要：境界の冪が中心に入れば中心は境界の補開集合を避ける。
方針：中心を含む素イデアルが境界元を含むことを使う。
規約：KST §5、Stacks 0815、正則性はこの包含には不要。
使われ方：イデアル加群を平坦化する blowup の admissible 条件。
-/
theorem basicOpen_le_affineCenterComplement_of_pow_mem :
    PrimeSpectrum.basicOpen f ≤ affineCenterComplement I := by
  intro x hx
  apply (mem_affineCenterComplement I x).mpr
  intro hI
  exact hx (x.isPrime.mem_of_pow_mem n (hI hn))

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
