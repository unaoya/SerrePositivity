module

public import SerrePositivity.AlgebraicGeometry.PureTransformExactPowers
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
概要：普遍単射から始まる短完全列を、ブローアップのチャート上の純変換へ移す。
方針：テンソル積を比較して普遍単射を底変換へ移し、境界元の冪による商に適用する。
規約：チャートの環と境界元を任意の基底代数とその元で表す。
使われ方：Stacks 0815 の次元帰納で、自由な左端を持つ列から平坦性を戻す。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open scoped TensorProduct

private theorem lTensor_baseChange_injective
    {R A M N Q : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup Q] [Module R Q] [Module A Q] [IsScalarTower R A Q]
    (g : M →ₗ[R] N) (hg : Function.Injective (g.lTensor Q)) :
    Function.Injective ((g.baseChange A).lTensor Q) := by
  let eM := TensorProduct.AlgebraTensorModule.cancelBaseChange R A A Q M
  let eN := TensorProduct.AlgebraTensorModule.cancelBaseChange R A A Q N
  have h := TensorProduct.AlgebraTensorModule.lTensor_comp_cancelBaseChange R A A (M := Q) g
  apply Function.Injective.of_comp (f := eN)
  change Function.Injective ⇑(eN.toLinearMap.comp
    (TensorProduct.AlgebraTensorModule.lTensor A Q
      (TensorProduct.AlgebraTensorModule.lTensor A A g)))
  rw [← h]
  exact hg.comp eM.injective

universe u

/--
概要：普遍単射を左端とする短完全列は、任意の基底変更の後に境界ねじれを除いても短完全。
方針：底変換した左端の普遍単射性を境界元の冪による商で使い、中央の完全性を得る。
規約：境界元は基底変更した環の元でよい。
使われ方：余核に帰納を適用するための純変換の短完全列。
-/
theorem pureTransform_baseChange_shortExact_of_universal_injective
    {A : Type u} {R M N P : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] (a : A) (g : M →ₗ[R] N) (h : N →ₗ[R] P)
    (hex : Function.Exact g h) (hsurj : Function.Surjective h)
    (hinj : ∀ (Q : Type u) [AddCommGroup Q] [Module R Q],
      Function.Injective (g.lTensor Q)) :
    Function.Injective (modulePureTransformMap a (g.baseChange A)) ∧
      Function.Exact (modulePureTransformMap a (g.baseChange A))
        (modulePureTransformMap a (h.baseChange A)) ∧
      Function.Surjective (modulePureTransformMap a (h.baseChange A)) := by
  refine ⟨modulePureTransformMap_injective a _ (hinj A), ?_,
    modulePureTransformMap_surjective a _ (h.lTensor_surjective A hsurj)⟩
  have hex' : Function.Exact (g.baseChange A) (h.baseChange A) := lTensor_exact A hex hsurj
  exact modulePureTransformMap_exact_of_quotient_lTensor_injective a _ _ hex'
    (fun k => lTensor_baseChange_injective g (hinj (A ⧸ Ideal.span {a ^ k})))

end SerrePositivity.AlgebraicGeometry
