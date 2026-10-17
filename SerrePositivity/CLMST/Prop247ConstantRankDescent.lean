module

public import SerrePositivity.CLMST.Prop247ConstantRankExcision
public import SerrePositivity.CLMST.Prop247RankTransport
public import SerrePositivity.CLMST.Prop247CoveredDescent
public import SerrePositivity.CommutativeAlgebra.EtaleAwayTensorBaseChange

/-! # Prop 2.4.7：定 rank の実 André 底変換から元の錐へ

元の rank は底変換で保存し、実通常 tensor の perfectoid 化と有限被覆を選ぶ。
全剰余段の共通指数と元の錐への降下は既存 D1〜D6 を使用する。
未供給の excision は明示仮定とし、既存 B-I のみを選択に使用する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.CLMST
open DerivedCompletion
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- 原典の定 rank の場合、指定した André 拡大と KL の excision 入力から元の実錐へ降下する。
始域 S の元の bounded torsion のみを使い、底変換後の bounded torsion は要求しない。 -/
theorem prop247_constantRank_isogeny_of_andre_excision
    (R S B C : Type u) [CommRing R] [CommRing S] [CommRing B] [CommRing C]
    [Algebra R S] [Algebra R B] [Algebra R C]
    [Module.Finite R S] [Algebra.FinitePresentation R S]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p) (hB : IsIntegralPerfectoid B p)
    (hAIC : IsAbsolutelyIntegrallyClosed B) (hExcision : KLFiniteComparisonExcision B p)
    (hflat : IsCompletelyFaithfullyFlat (Ideal.span {(p : R)})
      (baseChangeScalarModule (algebraMap R B)))
    (f : S →ₐ[R] C) (hf : IsPerfectoidization p f.toRingHom)
    (hbounded : ∃ N : ℕ, ∀ n : ℕ, ∀ s : S,
      (p : S) ^ n * s = 0 → (p : S) ^ N * s = 0)
    (g : R) (hetale : letI := GenericEtale.awayAlgebra R S g
      Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap R S g)))
    (r : ℕ) (hRank : ∀ x : PrimeSpectrum.basicOpen g, prop247_awayRank R S g x = r) :
    ∃ q : ℕ, moduleMapConeScalar R f.toLinearMap (g ^ q) = 0 ∧
      (∀ x : f.toLinearMap.ker, g ^ q • x = 0) ∧
      (∀ y : C ⧸ f.toLinearMap.range, g ^ q • y = 0) := by
  obtain ⟨P, hP, β₀, hβ₀⟩ :=
    BhattScholze.Inputs.exists_perfectoidization_of_integral B (B ⊗[R] S) p hB
  letI := hP
  letI : Algebra B P := (β₀.comp (algebraMap B (B ⊗[R] S))).toAlgebra
  let β : B ⊗[R] S →ₐ[B] P := { β₀ with commutes' := fun _ => rfl }
  have hβ : IsPerfectoidization p β.toRingHom := hβ₀
  have hetaleB := etaleAway_tensor_baseChange (R := R) (A := S) (B := B) g hetale
  have hRankB := prop247_awayRank_baseChange_constant R S B g hetale r hRank
  have hfixed := prop247_aic_constantRank_isogeny_of_finiteComparison_excision
    p hB hAIC hExcision (algebraMap R B g) β hβ hetaleB r hRankB
  have hU := prop247_uniform_of_standard_fixed_cone R S B C P p hR hB f hf hbounded
    g β hβ hflat.1 hfixed
  exact moduleMapConeIsogeny_descent (algebraMap R B) (p : R) hflat f.toLinearMap
    (prop247_cone_isComplete_of_perfectoid_target R S p hR C hf.1 f.toLinearMap) g hU

end SerrePositivity.CLMST
