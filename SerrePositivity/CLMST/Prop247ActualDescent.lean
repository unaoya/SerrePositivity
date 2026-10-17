module

public import SerrePositivity.CLMST.Prop247UniformStandard

/-! # Prop 2.4.7：実標準比較を構成した上での元の錐への降下

残る入力は通常 tensor と有限自由加群の実共通比較、およびその almost 零化である。
始域・終域・錐・全剰余段の比較同型は追加仮定にしない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.CLMST
open CategoryTheory DerivedCompletion
open scoped TensorProduct
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- 元の実 perfectoid 化写像に対し、通常 tensor 上の共通比較から同じ元の錐へ降下する。
大域的な自由比較の存在を主張するものではなく、各局所比較への適用入口。 -/
theorem prop247_isogeny_of_actual_common_comparison
    (R S B C E : Type u) [CommRing R] [CommRing S] [CommRing B] [CommRing C]
    [Algebra R S] [Algebra R B] [Algebra B C]
    [AddCommGroup E] [Module B E]
    [Module.Finite R S] [Algebra.FinitePresentation R S]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (hB : IsIntegralPerfectoid B p)
    (hflat : IsCompletelyFaithfullyFlat (Ideal.span {(p : R)})
      (baseChangeScalarModule (algebraMap R B)))
    (hbounded : ∃ N : ℕ, ∀ n : ℕ, ∀ s : S,
      (p : S) ^ n * s = 0 → (p : S) ^ N * s = 0)
    (g : R) (r : ℕ) (β : B ⊗[R] S →ₐ[B] C)
    (hβ : IsPerfectoidization p β.toRingHom)
    (u : (B ⊗[R] S) →ₗ[B] (Fin r → B))
    (v : C →ₗ[B] E) (w : (Fin r → B) →ₗ[B] E)
    (hsq : v.comp β.toLinearMap = w.comp u)
    (hu : Function.Bijective (awayModuleMap (algebraMap R B g) u))
    (hv : ∀ y : C, v y = 0 → algebraMap R B g • y = 0)
    (hw : ∀ z : (Fin r → B), w z = 0 → algebraMap R B g • z = 0)
    (hcw : ∀ y : E ⧸ w.range, algebraMap R B g • y = 0) :
    ∃ N : ℕ, moduleMapConeScalar R (perfectoidizationModuleMap R S p hR) (g ^ N) = 0 ∧
      (∀ x : (perfectoidizationModuleMap R S p hR).ker, g ^ N • x = 0) ∧
      (∀ x : Perfectoidization R S p hR ⧸
        (perfectoidizationModuleMap R S p hR).range, g ^ N • x = 0) := by
  let f := IsScalarTower.toAlgHom R S (Perfectoidization R S p hR)
  have hf : IsPerfectoidization p f.toRingHom :=
    isPerfectoidization_toPerfectoidization R S p hR
  exact prop247_isogeny_of_standard_comparison R S B (Perfectoidization R S p hR) C E
    p hR hB f hf hbounded g r β hβ u v w hsq hu hv hw hcw hflat

end SerrePositivity.CLMST
