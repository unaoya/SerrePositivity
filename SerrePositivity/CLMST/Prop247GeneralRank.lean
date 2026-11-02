module

public import SerrePositivity.CLMST.Prop247AndreBase
public import SerrePositivity.CLMST.Prop247RankData
public import SerrePositivity.CLMST.Prop247CoveredDescent
public import SerrePositivity.CommutativeAlgebra.Localization.EtaleAway

/-! # Prop 2.4.7：一般 rank の実データから元の錐への条件付き接続

André 拡大、通常 tensor の perfectoid 化、原典の有限 rank 分解と各普遍単位を選ぶ。
残る終域比較の核の冪零化は、その実データの元の写像について明示する。
全剰余段への共通指数と元の錐への降下を既存 D1〜D6 へ接続する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.CLMST
open DerivedCompletion
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- 原典の一般 rank の実対象を全て選び、残る終域比較から元の実錐へ降下する。
André 拡大・rank 対象・各 perfectoid 化の存在は追加仮定にしない。 -/
theorem prop247_exists_generalRank_descent_data
    (R S C : Type u) [CommRing R] [CommRing S] [CommRing C]
    [Algebra R S] [Algebra R C] [Module.Finite R S] [Algebra.FinitePresentation R S]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (hExcision : ∀ (B : Type u) [CommRing B], IsIntegralPerfectoid B p →
      IsAbsolutelyIntegrallyClosed B → KLFiniteComparisonExcision B p)
    (f : S →ₐ[R] C) (hf : IsPerfectoidization p f.toRingHom)
    (hbounded : ∃ N : ℕ, ∀ n : ℕ, ∀ s : S,
      (p : S) ^ n * s = 0 → (p : S) ^ N * s = 0)
    (g : R) (hetale : letI := GenericEtale.awayAlgebra R S g
      Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap R S g))) :
    ∃ (B : CommAlgCat.{u} R),
      let hetaleB := etaleAway_tensor_baseChange (R := R) (A := S) (B := B) g hetale
      ∃ (_ : IsIntegralPerfectoid B p) (_ : IsAbsolutelyIntegrallyClosed B)
        (_ : IsCompletelyFaithfullyFlat (Ideal.span {(p : R)})
          (baseChangeScalarModule (algebraMap R B)))
        (P : CommAlgCat.{u} B) (β : B ⊗[R] S →ₐ[B] P)
        (hβ : IsPerfectoidization p β.toRingHom)
        (t : Finset ℕ)
        (_ : ∀ x : PrimeSpectrum.basicOpen (algebraMap R B g),
          awayRank B (B ⊗[R] S) (algebraMap R B g) x ∈ t)
        (T : t → CommAlgCat.{u} B)
        (u : ∀ n : t, prop247_rankSourceImage B (B ⊗[R] S)
          (algebraMap R B g) hetaleB n →ₐ[B] T n)
        (_ : ∀ n : t, IsPerfectoidization p (u n).toRingHom)
        (Q : t → CommAlgCat.{u} B)
        (γ : ∀ n : t, T n ⊗[B] (B ⊗[R] S) →ₐ[B] Q n)
        (hγ : ∀ n : t, IsPerfectoidization p (γ n).toRingHom),
        (∃ b : ℕ, ∀ x : (prop247_rankPerfectoidComparison B (B ⊗[R] S)
          (fun n => T n) p P β hβ (fun n => Q n) γ hγ).toLinearMap.ker,
          (algebraMap R B g) ^ b • x = 0) →
        ∃ q : ℕ, moduleMapConeScalar R f.toLinearMap (g ^ q) = 0 ∧
          (∀ x : f.toLinearMap.ker, g ^ q • x = 0) ∧
          (∀ y : C ⧸ f.toLinearMap.range, g ^ q • y = 0) := by
  obtain ⟨B, hB, hRB, hperf, hAIC, hflat⟩ := prop247_exists_andre_descent_base R p hR
  letI := hB
  letI := hRB
  let A := B ⊗[R] S
  obtain ⟨P, hP, β₀, hβ₀⟩ := BhattScholze.Inputs.exists_perfectoidization_of_integral B A p hperf
  letI := hP
  letI : Algebra B P := (β₀.comp (algebraMap B A)).toAlgebra
  let β : A →ₐ[B] P := { β₀ with commutes' := fun _ => rfl }
  have hβ : IsPerfectoidization p β.toRingHom := hβ₀
  have hetaleB := etaleAway_tensor_baseChange (R := R) (A := S) (B := B) g hetale
  obtain ⟨t, hcover, T, u, hu, Q, γ, hγ, hassembly⟩ :=
    prop247_aic_exists_rank_comparison_data B A P p hperf hAIC hExcision
      (algebraMap R B g) hetaleB β hβ
  refine ⟨CommAlgCat.of R B, hperf, hAIC, hflat, CommAlgCat.of B P,
    β, hβ, t, hcover, T, u, hu, Q, γ, hγ, ?_⟩
  intro htk
  obtain ⟨q, hq, _hk, _hc⟩ := hassembly htk
  have hU := prop247_uniform_of_standard_fixed_cone R S B C P p hR hperf f hf hbounded
    g β hβ hflat.1 ⟨q, hq⟩
  exact moduleMapConeIsogeny_descent (algebraMap R B) (p : R) hflat f.toLinearMap
    (prop247_cone_isComplete_of_perfectoid_target R S p hR C hf.1 f.toLinearMap) g hU

end SerrePositivity.CLMST
