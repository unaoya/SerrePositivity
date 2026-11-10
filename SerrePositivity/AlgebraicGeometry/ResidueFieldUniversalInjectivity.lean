module

public import SerrePositivity.AlgebraicGeometry.LocalUniversalInjectivity
public import SerrePositivity.AlgebraicGeometry.ResidueTensorUniversalInjectivity
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
概要：各極大点での剰余体テンソルの単射性から普遍単射性を得る。
方針：局所化と剰余体への底変換を一段にまとめ、局所基底の判定を適用する。
規約：始域は射影、標的は平坦とする。
使われ方：全ファイバーで生成点の基底を与える写像の普遍単射性を示す。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open scoped TensorProduct

/--
概要：射影加群から平坦加群への写像が各極大点の剰余体への底変換で単射なら、普遍単射。
方針：局所基底の剰余体判定を使い、すべての極大点から単射性を戻す。
規約：剰余体は極大イデアルで局所化した局所環の剰余体とする。
使われ方：Stacks 0815 で全ファイバーの生成点の単射性を普遍単射性に移す。
-/
theorem lTensor_injective_of_residueFields_of_projective
    {R M N : Type u} [CommRing R] [AddCommGroup M] [Module R M] [Module.Projective R M]
    [AddCommGroup N] [Module R N] [Module.Flat R N]
    (f : M →ₗ[R] N)
    (hf : ∀ (p : Ideal R) [p.IsMaximal], Function.Injective (f.lTensor p.ResidueField))
    (Q : Type v) [AddCommGroup Q] [Module R Q] :
    Function.Injective (f.lTensor Q) := by
  refine lTensor_injective_of_lTensor_baseChange_atMaximal f ?_ Q
  intro p hp A _ _
  let S := Localization.AtPrime p
  let k := p.ResidueField
  let eM := TensorProduct.AlgebraTensorModule.cancelBaseChange R S S k M
  let eN := TensorProduct.AlgebraTensorModule.cancelBaseChange R S S k N
  have he : ⇑(f.lTensor k) ∘ ⇑eM = ⇑eN ∘ ⇑((f.baseChange S).lTensor k) :=
    congrArg DFunLike.coe
      (TensorProduct.AlgebraTensorModule.lTensor_comp_cancelBaseChange R S S (M := k) f)
  have hinj : Function.Injective ((f.baseChange S).lTensor k) := by
    apply Function.Injective.of_comp (f := eN)
    rw [← he]
    exact (hf p).comp eM.injective
  exact lTensor_injective_of_residueTensor_injective_of_projective (f.baseChange S) hinj A

end SerrePositivity.AlgebraicGeometry
