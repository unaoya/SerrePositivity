module

public import SerrePositivity.CLMST.Prop247RankAssembly
public import SerrePositivity.CLMST.Prop247CoveredDescent

/-! # Prop 2.4.7：André 底変換後の実 rank 比較から元の錐へ降下

rank 比較の元の写像を構成し、全剰余段に共通する指数を既存 D1〜D6 へ渡す。
Cor 8.12 と KL-T から来る実 almost 零化と各成分の isogeny は明示入力である。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.CLMST
open DerivedCompletion
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- 元の S と指定 perfectoid 化に対し、実 rank 比較から元の実錐・核・余核へ降下する。
未知の可換式や各剰余段の比較を仮定せず、全て元の標準構成から供給する。 -/
theorem prop247_isogeny_of_standard_rank_comparisons
    (R S B C P : Type u) [CommRing R] [CommRing S] [CommRing B] [CommRing C] [CommRing P]
    [Algebra R S] [Algebra R B] [Algebra R C] [Algebra B P]
    [Module.Finite R S] [Algebra.FinitePresentation R S]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p) (hB : IsIntegralPerfectoid B p)
    (f : S →ₐ[R] C) (hf : IsPerfectoidization p f.toRingHom)
    (hbounded : ∃ N : ℕ, ∀ n : ℕ, ∀ s : S,
      (p : S) ^ n * s = 0 → (p : S) ^ N * s = 0)
    (hflat : IsCompletelyFaithfullyFlat (Ideal.span {(p : R)})
      (baseChangeScalarModule (algebraMap R B)))
    (g : R) (β : B ⊗[R] S →ₐ[B] P) (hβ : IsPerfectoidization p β.toRingHom)
    {ι : Type u} [Finite ι] (T Q : ι → Type u)
    [∀ i, CommRing (T i)] [∀ i, Algebra B (T i)]
    [∀ i, CommRing (Q i)] [∀ i, Algebra B (Q i)]
    (γ : ∀ i, T i ⊗[B] (B ⊗[R] S) →ₐ[B] Q i)
    (hγ : ∀ i, IsPerfectoidization p (γ i).toRingHom)
    (a b : ℕ)
    (hk : ∀ x : (Algebra.linearMap B ((i : ι) → T i)).ker, (algebraMap R B g) ^ a • x = 0)
    (hc : ∀ y : ((i : ι) → T i) ⧸ (Algebra.linearMap B ((i : ι) → T i)).range,
      (algebraMap R B g) ^ a • y = 0)
    (htk : ∀ x : (prop247_rankPerfectoidComparison B (B ⊗[R] S) T p P β hβ Q γ hγ).toLinearMap.ker,
      (algebraMap R B g) ^ b • x = 0)
    (hcomponent : ∀ i, ∃ q : ℕ,
      (∀ x : (γ i).toLinearMap.ker, (algebraMap R B g) ^ q • x = 0) ∧
        (∀ y : Q i ⧸ (γ i).toLinearMap.range, (algebraMap R B g) ^ q • y = 0)) :
    ∃ q : ℕ, moduleMapConeScalar R f.toLinearMap (g ^ q) = 0 ∧
      (∀ x : f.toLinearMap.ker, g ^ q • x = 0) ∧
      (∀ y : C ⧸ f.toLinearMap.range, g ^ q • y = 0) := by
  have hfixed := prop247_isogeny_of_actual_rank_comparisons B (B ⊗[R] S) T p P β hβ Q γ hγ
    (algebraMap R B g) a b hk hc htk hcomponent
  have hU := prop247_uniform_of_standard_fixed_cone R S B C P p hR hB f hf hbounded
    g β hβ hflat.1 hfixed
  exact moduleMapConeIsogeny_descent (algebraMap R B) (p : R) hflat f.toLinearMap
    (prop247_cone_isComplete_of_perfectoid_target R S p hR C hf.1 f.toLinearMap) g hU

end SerrePositivity.CLMST
