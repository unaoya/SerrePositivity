module

public meta import SerrePositivity.Util.DeprecatedAlias
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
概要：KST §5、Stacks 05C2 の平坦テンソルの随伴素イデアルの素剰余への帰着。
方針：素イデアル剰余による Noether 加群の帰納原理を、平坦テンソルした完全列で閉じる。
規約：この段階は R/p への帰着で、剰余体への局所化は別の比較。
使われ方：Stacks 05DM のファイバー条件から有限試験の随伴素イデアル条件を得る。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct

/--
概要：有限加群の平坦テンソルの随伴素イデアルの包含は、素イデアル剰余だけで試験できる。
方針：素剰余による帰納原理と、短完全列の中項の随伴素イデアルの包含を使う。
規約：KST §5、Stacks 05C2, Lemma 10.65.5 の包含側の準備。S の Noether 性は不要。
使われ方：元の基礎環の各素イデアルに対するファイバー条件への帰着。
-/
theorem associatedPrimes_tensorProduct_subset_of_prime_quotients
    {R S N : Type u} [CommRing R] [IsNoetherianRing R] [CommRing S] [Algebra R S]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N] [Module.Flat R N]
    (U : Set (Ideal S))
    (hU : ∀ p : Ideal R, p.IsPrime → associatedPrimes S (N ⊗[R] (R ⧸ p)) ⊆ U)
    (Q : Type u) [AddCommGroup Q] [Module R Q] [Module.Finite R Q] :
    associatedPrimes S (N ⊗[R] Q) ⊆ U := by
  apply IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime R
    (inferInstance : Module.Finite R Q)
    (motive := fun P _ _ _ => associatedPrimes S (N ⊗[R] P) ⊆ U)
  · intro P hP hRP hfin hsub p hp
    exact (not_isAssociatedPrime_of_subsingleton hp).elim
  · intro P hP hRP hfin p e q hq
    let E := TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl S N) e
    exact hU p.asIdeal p.isPrime (hq.map_of_injective E.toLinearMap E.injective)
  · intro P₁ hP₁ hRP₁ hfin₁ P₂ hP₂ hRP₂ hfin₂ P₃ hP₃ hRP₃ hfin₃ f g hf hg hfg h₁ h₃ p hp
    have hbound := associatedPrimes.subset_union_of_exact
      (f := TensorProduct.AlgebraTensorModule.lTensor S N f)
      (g := TensorProduct.AlgebraTensorModule.lTensor S N g)
      (Module.Flat.lTensor_preserves_injective_linearMap f hf) (Module.Flat.lTensor_exact N hfg)
    rcases hbound hp with h | h
    · exact h₁ h
    · exact h₃ h

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
