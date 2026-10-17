module

public import SerrePositivity.CLMST.Prop247RankComponentExcision
public import Mathlib.Algebra.Category.CommAlgCat.Basic

/-! # Prop 2.4.7：原典の実 rank 比較データの選択

有限 rank 集合、元の Ri の指定 perfectoid 化、各 Si の指定 perfectoid 化を構成する。
残る終域比較の核の冪零化を、これらの実対象について明示する。
存在の選択には既存 B3 と既存 B-I を使用し、新しい入力は追加しない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.CLMST
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- 原典の実 rank 対象と単位を選び、終域比較の核の冪零化から元の錐へ接続する。
各対象の元の R 代数構造は CommAlgCat に保持し、対象の存在を仮定しない。 -/
theorem prop247_aic_exists_rank_comparison_data
    (R S C : Type u) [CommRing R] [CommRing S] [CommRing C]
    [Algebra R S] [Algebra R C] [Module.Finite R S] [Algebra.FinitePresentation R S]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (hAIC : IsAbsolutelyIntegrallyClosed R)
    (hExcision : ∀ (B : Type u) [CommRing B], IsIntegralPerfectoid B p →
      IsAbsolutelyIntegrallyClosed B → KLFiniteComparisonExcision B p)
    (g : R) (hetale : letI := GenericEtale.awayAlgebra R S g
      Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap R S g)))
    (f : S →ₐ[R] C) (hf : IsPerfectoidization p f.toRingHom) :
    ∃ (t : Finset ℕ) (_ : ∀ x : PrimeSpectrum.basicOpen g, prop247_awayRank R S g x ∈ t)
      (T : t → CommAlgCat.{u} R)
      (u : ∀ n : t, prop247_rankSourceImage R S g hetale n →ₐ[R] T n)
      (_ : ∀ n : t, IsPerfectoidization p (u n).toRingHom)
      (P : t → CommAlgCat.{u} R)
      (β : ∀ n : t, T n ⊗[R] S →ₐ[R] P n)
      (hβ : ∀ n : t, IsPerfectoidization p (β n).toRingHom),
      (∃ b : ℕ, ∀ x : (prop247_rankPerfectoidComparison R S
        (fun n => T n) p C f hf (fun n => P n) β hβ).toLinearMap.ker, g ^ b • x = 0) →
      ∃ q : ℕ, moduleMapConeScalar R f.toLinearMap (g ^ q) = 0 ∧
        (∀ x : f.toLinearMap.ker, g ^ q • x = 0) ∧
        (∀ y : C ⧸ f.toLinearMap.range, g ^ q • y = 0) := by
  classical
  obtain ⟨t, _ht, _hc, hcover, _hd⟩ :=
    prop247_awayRank_finite_clopen_decomposition R S g hetale
  have htargets (n : t) : ∃ (T : CommAlgCat.{u} R)
      (u : prop247_rankSourceImage R S g hetale n →ₐ[R] T),
      IsPerfectoidization p u.toRingHom := by
    obtain ⟨T, hT, hRT, hIT, htower, hf, _hs, _hfin, _hrank⟩ :=
      prop247_rankImage_exists_perfectoid_target R S p hR g hetale n
    letI := hT
    letI := hRT
    letI := hIT
    letI := htower
    exact ⟨CommAlgCat.of R T,
      IsScalarTower.toAlgHom R (prop247_rankSourceImage R S g hetale n) T, hf⟩
  choose T u hu using htargets
  letI (n : t) : Algebra (prop247_rankSourceImage R S g hetale n) (T n) :=
    (u n).toRingHom.toAlgebra
  letI (n : t) : IsScalarTower R (prop247_rankSourceImage R S g hetale n) (T n) :=
    IsScalarTower.of_algHom (u n)
  have hT (n : t) : IsPerfectoidization p
      (algebraMap (prop247_rankSourceImage R S g hetale n) (T n)) := hu n
  have hperfectoid (n : t) : ∃ (P : CommAlgCat.{u} R)
      (β : T n ⊗[R] S →ₐ[R] P), IsPerfectoidization p β.toRingHom := by
    obtain ⟨P, hP, β₀, hβ₀⟩ := BhattScholze.Inputs.exists_perfectoidization_of_integral
      (T n) (T n ⊗[R] S) p (hT n).1
    letI := hP
    letI : Algebra R P := (β₀.comp (algebraMap R (T n ⊗[R] S))).toAlgebra
    exact ⟨CommAlgCat.of R P, { β₀ with commutes' := fun _ => rfl }, hβ₀⟩
  choose P β hβ using hperfectoid
  refine ⟨t, hcover, T, u, hu, P, β, hβ, ?_⟩
  intro htk
  apply prop247_aic_isogeny_of_rank_component_excision R S p hR hAIC g hetale t hcover
    (fun n => T n) hT ?_ C f hf (fun n => P n) β hβ htk
  intro n
  exact hExcision (T n) (hT n).1
    (prop247_rankTarget_isAbsolutelyIntegrallyClosed R S p hR hAIC g hetale n (T n) (hT n))

end SerrePositivity.CLMST
