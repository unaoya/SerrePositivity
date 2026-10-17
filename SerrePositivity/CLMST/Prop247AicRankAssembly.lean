module

public import SerrePositivity.CLMST.Prop247AicRankCoefficients
public import SerrePositivity.CLMST.Prop247RankAssembly

/-! # Prop 2.4.7：André 基底上の実 rank 係数入力を供給した組立て

係数比較の核・余核の冪零化は原典の rank 像から証明する。
終域比較の核と各成分の isogeny は明示入力として保持する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.CLMST
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- 絶対整閉基底上では、残る終域比較と成分 isogeny から元の実錐へ合流する。
係数比較の冪零化・可換式・有限成分の共通指数は構成する。 -/
theorem prop247_aic_isogeny_of_rank_comparisons
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (hAIC : IsAbsolutelyIntegrallyClosed R) (g : R)
    (hetale : letI := GenericEtale.awayAlgebra R S g
      Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap R S g)))
    (t : Finset ℕ) (ht : ∀ x : PrimeSpectrum.basicOpen g, prop247_awayRank R S g x ∈ t)
    (T : t → Type u) [∀ n : t, CommRing (T n)] [∀ n : t, Algebra R (T n)]
    [∀ n : t, Algebra (prop247_rankSourceImage R S g hetale n) (T n)]
    [∀ n : t, IsScalarTower R (prop247_rankSourceImage R S g hetale n) (T n)]
    (hT : ∀ n : t, IsPerfectoidization p
      (algebraMap (prop247_rankSourceImage R S g hetale n) (T n)))
    (C : Type u) [CommRing C] [Algebra R C]
    (f : S →ₐ[R] C) (hf : IsPerfectoidization p f.toRingHom)
    (P : t → Type u) [∀ n : t, CommRing (P n)] [∀ n : t, Algebra R (P n)]
    (β : ∀ n : t, T n ⊗[R] S →ₐ[R] P n)
    (hβ : ∀ n : t, IsPerfectoidization p (β n).toRingHom)
    (htk : ∃ b : ℕ, ∀ x :
      (prop247_rankPerfectoidComparison R S T p C f hf P β hβ).toLinearMap.ker,
      g ^ b • x = 0)
    (hcomponent : ∀ n : t, ∃ q : ℕ,
      (∀ x : (β n).toLinearMap.ker, g ^ q • x = 0) ∧
        (∀ y : P n ⧸ (β n).toLinearMap.range, g ^ q • y = 0)) :
    ∃ q : ℕ, moduleMapConeScalar R f.toLinearMap (g ^ q) = 0 ∧
      (∀ x : f.toLinearMap.ker, g ^ q • x = 0) ∧
      (∀ y : C ⧸ f.toLinearMap.range, g ^ q • y = 0) := by
  obtain ⟨a, hk, hc⟩ :=
    prop247_aic_rankCoefficient_annihilators R S p hR hAIC g hetale t ht T hT
  obtain ⟨b, htk⟩ := htk
  obtain ⟨q, hq⟩ := prop247_isogeny_of_actual_rank_comparisons R S T p C f hf P β hβ
    g a b hk hc htk hcomponent
  obtain ⟨hfk, hfc⟩ := moduleMapCone_pow_scalar_eq_zero_annihilates R f.toLinearMap g q hq
  exact ⟨q, hq, hfk, hfc⟩

end SerrePositivity.CLMST
