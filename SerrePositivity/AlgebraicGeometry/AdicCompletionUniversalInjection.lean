module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.AssociatedPrimeAdicSeparation
public import SerrePositivity.AlgebraicGeometry.AdicTensorRightComparison
public import SerrePositivity.AlgebraicGeometry.FiniteTensorTest
public import SerrePositivity.CommutativeAlgebra.Adic.Completion.Tensor

/-!
概要：KST §5、Stacks 05DL の平坦加群の場合の完備化への普遍単射性。
方針：随伴素イデアルによる分離性を各有限テンソルに適用し、完備化の平坦性で試験を広げる。
規約：05DM のファイバー条件から有限試験の随伴素イデアル条件への移行は別工程。
使われ方：原典 05DP の完備化から元の加群への Mittag–Leffler 性の降下。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct

/--
概要：拡大イデアルに対する随伴素イデアルの条件から、元の環上の完備化への単射性を得る。
方針：拡大イデアルでの完備化の単射性を既存のスカラー制限比較で移す。
規約：KST §5、Stacks 05DL、Noether 性は作用する大きい環だけに要求する。
使われ方：元の加群の有限テンソルの完備化への単射性。
-/
theorem adicCompletion_of_injective_of_associatedPrimes_restrict
    {R S N : Type u} [CommRing R] [CommRing S] [Algebra R S] [IsNoetherianRing S]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N] [Module.Finite S N]
    (I : Ideal R)
    (hAss : ∀ p : Ideal S, p ∈ associatedPrimes S N → I.map (algebraMap R S) ⊔ p ≠ ⊤) :
    Function.Injective (AdicCompletion.of I N) := by
  have hS := adicCompletion_of_injective_of_associatedPrimes (I.map (algebraMap R S)) hAss
  intro x y hxy
  apply hS
  apply (SerrePositivity.adicCompletionScalarRestrictionEquiv (S := S) (M := N) I).injective
  simpa only [SerrePositivity.adicCompletionScalarRestrictionEquiv_of] using hxy

/--
概要：有限試験の全随伴素イデアルが中心と互いに素でなければ、平坦加群の完備化写像は普遍単射。
方針：各有限テンソルの分離性を完備化比較の因子化で戻し、平坦な終域への有限試験を使う。
規約：KST §5、Stacks 05DL の R 平坦性を追加した形。05DM のファイバー条件の比較は含めない。
使われ方：完備化の Mittag–Leffler 性を元の加群へ戻す際の普遍単射性。
-/
theorem adicCompletion_of_rTensor_injective_of_associatedPrimes_tests
    {R S N : Type u} [CommRing R] [IsNoetherianRing R]
    [CommRing S] [Algebra R S] [IsNoetherianRing S]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    [Module.Finite S N] [Module.Flat R N] (I : Ideal R)
    (hAss : ∀ (Q : Type u) [AddCommGroup Q] [Module R Q] [Module.Finite R Q],
      ∀ p : Ideal S, p ∈ associatedPrimes S (N ⊗[R] Q) →
        I.map (algebraMap R S) ⊔ p ≠ ⊤)
    (Q : Type u) [AddCommGroup Q] [Module R Q] :
    Function.Injective ((AdicCompletion.of I N).rTensor Q) := by
  let := SerrePositivity.flat_adicCompletion_of_flat (P := N) I
  have hfinite (P : Type u) [AddCommGroup P] [Module R P] [Module.Finite R P] :
      Function.Injective ((AdicCompletion.of I N).lTensor P) := by
    let := finite_tensorProduct_over_left_algebra (R := R) (S := S) (N := N) (Q := P)
    have hinj := adicCompletion_of_injective_of_associatedPrimes_restrict
      (R := R) (S := S) (N := N ⊗[R] P) I (hAss P)
    have hright : Function.Injective ((AdicCompletion.of I N).rTensor P) := by
      intro x y hxy
      apply hinj
      have h := congrArg (adicCompletionTensorRightComparison (N := N) (Q := P) I) hxy
      change ((adicCompletionTensorRightComparison (N := N) (Q := P) I).comp
        ((AdicCompletion.of I N).rTensor P)) x =
        ((adicCompletionTensorRightComparison (N := N) (Q := P) I).comp
          ((AdicCompletion.of I N).rTensor P)) y at h
      rwa [adicCompletionTensorRightComparison_comp_of] at h
    exact ((AdicCompletion.of I N).lTensor_inj_iff_rTensor_inj P).mpr hright
  exact ((AdicCompletion.of I N).lTensor_inj_iff_rTensor_inj Q).mp
    (lTensor_injective_of_finite_tests (AdicCompletion.of I N) hfinite Q)

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
