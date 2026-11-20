module

public import SerrePositivity.CommutativeAlgebra.Adic.Completion.Tensor
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.TensorProduct.Finite

/-!
概要：KST §5、Stacks 05DL の有限テンソル試験と右テンソルの完備化比較。
方針：有限自由全射で有限性を確認し、既存の比較を左右交換して因子化式を得る。
規約：CommutativeAlgebra の既証の比較を読み取り専用で使う。
使われ方：随伴素イデアルによる分離性から完備化写像の普遍単射性へ進む。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct

/--
概要：S 上有限な N と R 上有限な Q の R テンソル積は、左因子の作用で S 上有限。
方針：Q への有限自由全射をテンソルし、有限個の N の積からの全射を構成する。
規約：KST §5、Stacks 05DL、R→S は有限型を要求しない。
使われ方：有限試験加群とのテンソルへの Artin–Rees の適用。
-/
theorem finite_tensorProduct_over_left_algebra
    {R S N Q : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    [AddCommGroup Q] [Module R Q] [Module.Finite S N] [Module.Finite R Q] :
    Module.Finite S (N ⊗[R] Q) := by
  classical
  obtain ⟨n, q, hq⟩ := Module.Finite.exists_fin' R Q
  let e := TensorProduct.piScalarRight R S N (Fin n)
  let := Module.Finite.equiv e.symm
  exact Module.Finite.of_surjective (TensorProduct.AlgebraTensorModule.lTensor S N q)
    (LinearMap.lTensor_surjective N hq)

/--
概要：右テンソルを使う形の完備化・テンソル比較写像。
方針：既存の比較の前後でテンソル積を交換する。
規約：KST §5、Stacks 05DL、比較の定義には有限性や Noether 性を要求しない。
使われ方：元の加群の完備化写像の右テンソルの因子化。
-/
def adicCompletionTensorRightComparison
    {R N Q : Type u} [CommRing R] [AddCommGroup N] [Module R N]
    [AddCommGroup Q] [Module R Q] (I : Ideal R) :
    (AdicCompletion I N) ⊗[R] Q →ₗ[R] AdicCompletion I (N ⊗[R] Q) :=
  (((AdicCompletion.congr I (TensorProduct.comm R Q N)).restrictScalars R).toLinearMap.comp
    (SerrePositivity.adicCompletionTensorComparison I Q N)).comp
      (TensorProduct.comm R (AdicCompletion I N) Q).toLinearMap

/--
概要：右テンソルの完備化比較は、元の標準完備化写像と可換。
方針：純テンソルで既存の比較と完備化の自然性を計算する。
規約：KST §5、Stacks 05DL、実際の線形写像の等式。
使われ方：テンソルの完備化への単射性を、完備化写像のテンソルへ戻す。
-/
theorem adicCompletionTensorRightComparison_comp_of
    {R N Q : Type u} [CommRing R] [AddCommGroup N] [Module R N]
    [AddCommGroup Q] [Module R Q] (I : Ideal R) :
    (adicCompletionTensorRightComparison (N := N) (Q := Q) I).comp
      ((AdicCompletion.of I N).rTensor Q) = AdicCompletion.of I (N ⊗[R] Q) := by
  apply TensorProduct.ext'
  intro n q
  change AdicCompletion.map I (TensorProduct.comm R Q N).toLinearMap
    (AdicCompletion.map I (TensorProduct.mk R Q N q) (AdicCompletion.of I N n)) = _
  rw [AdicCompletion.map_of, AdicCompletion.map_of]
  rfl

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
