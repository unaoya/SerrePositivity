module

public import SerrePositivity.CommutativeAlgebra.AdicCompletionBaseQuotient
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.TensorProduct.Quotient

/-! # 平坦代数とその完備化の冪商の平坦性

商への基底変換はMathlibのテンソル積同型を使用する。
完備化の全冪商の平坦性を元の代数から導く。完備化全体の平坦性は別の課題。
-/

public section
namespace SerrePositivity
variable {B S : Type*} [CommRing B] [CommRing S] [Algebra B S]

/-- 平坦代数の商は、基底の同じイデアルによる商上で平坦。 -/
theorem flat_quotient_of_flat_algebra [Module.Flat B S] (I : Ideal B) :
    Module.Flat (B ⧸ I) (S ⧸ I.map (algebraMap B S)) :=
  (Module.Flat.equiv_iff
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S I).toLinearEquiv).mpr inferInstance

/-- 有限生成イデアルに沿う完備化の全冪商は、元の代数の平坦性から平坦となる。
Noether性は不要。完備化C自体のB上の平坦性はこの定理の結論ではない。 -/
theorem adicCompletionBasePowQuotient_flat [Module.Flat B S]
    (I : Ideal B) (hI : I.FG) (n : ℕ) :
    let C := AdicCompletion (I.map (algebraMap B S)) S
    Module.Flat (B ⧸ (I ^ n)) (C ⧸ (I ^ n).map (algebraMap B C)) :=
  (Module.Flat.equiv_iff (adicCompletionBasePowQuotientEquiv (S := S) I hI n).toLinearEquiv).mpr
    (flat_quotient_of_flat_algebra (S := S) (I ^ n))

end SerrePositivity
