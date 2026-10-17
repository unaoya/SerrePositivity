module

public import SerrePositivity.CLMST.Prop247AicRankImages
public import SerrePositivity.CLMST.Prop247RankBaseChangeDiagram
public import SerrePositivity.CLMST.Prop247RankCone
public import SerrePositivity.HomologicalAlgebra.ConeComparisonSquare

/-! # Prop 2.4.7：André 基底上の実 rank 係数比較の冪零化

各 Ri の指定 perfectoid 化単位の全単射性により、通常の rank 直積の既存錐零化を
元の R→∏Ti へ移す。Cor 8.12 や終域比較の almost 零化は使用しない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.CLMST
set_option backward.isDefEq.respectTransparency false

/-- 原典の実 rank 係数写像の核・余核は、一つの g の冪で零化される。 -/
theorem prop247_aic_rankCoefficient_annihilators
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (hAIC : IsAbsolutelyIntegrallyClosed R) (g : R)
    (hetale : letI := GenericEtale.awayAlgebra R S g
      Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap R S g)))
    (t : Finset ℕ) (ht : ∀ x : PrimeSpectrum.basicOpen g, prop247_awayRank R S g x ∈ t)
    (T : t → Type u) [∀ n : t, CommRing (T n)] [∀ n : t, Algebra R (T n)]
    [∀ n : t, Algebra (prop247_rankSourceImage R S g hetale n) (T n)]
    [∀ n : t, IsScalarTower R (prop247_rankSourceImage R S g hetale n) (T n)]
    (hf : ∀ n : t, IsPerfectoidization p
      (algebraMap (prop247_rankSourceImage R S g hetale n) (T n))) :
    ∃ q : ℕ,
      (∀ x : (Algebra.linearMap R ((n : t) → T n)).ker, g ^ q • x = 0) ∧
      (∀ y : ((n : t) → T n) ⧸ (Algebra.linearMap R ((n : t) → T n)).range,
        g ^ q • y = 0) := by
  letI := hR.isReduced R p
  let u := (prop247_toRankImageProduct R S g hetale t).toLinearMap
  let e := (prop247_rankTargetProductMap R S g hetale t T).toLinearMap
  let f := Algebra.linearMap R ((n : t) → T n)
  have he : Function.Bijective e :=
    Function.Bijective.piMap (fun n : t =>
      prop247_aic_rankTarget_unit_bijective R S p hR hAIC g hetale n (T n)
        (algebraMap (prop247_rankSourceImage R S g hetale n) (T n)) (hf n))
  obtain ⟨q, hq⟩ := prop247_rankImageProduct_cone_isogeny R S g hetale t ht
  obtain ⟨huk, huc⟩ := moduleMapCone_pow_scalar_eq_zero_annihilates R u g q hq
  have hsq : (LinearMap.id : ((n : t) → T n) →ₗ[R] ((n : t) → T n)).comp f =
      e.comp u := by
    apply LinearMap.ext
    intro x
    exact (AlgHom.congr_fun (prop247_rankTargetProductMap_comp R S g hetale t T) x).symm
  have hek : ∀ x : e.ker, (1 : R) • x = 0 := by
    intro x
    apply Subtype.ext
    change (1 : R) • (x : prop247_rankImageProduct R S g hetale t) = 0
    simpa only [one_smul] using he.1 (x.property.trans (map_zero e).symm)
  have hec : ∀ y : ((n : t) → T n) ⧸ e.range, (1 : R) • y = 0 := by
    intro y
    obtain ⟨y, rfl⟩ := e.range.mkQ_surjective y
    obtain ⟨x, rfl⟩ := he.2 y
    rw [one_smul]
    exact (Submodule.Quotient.mk_eq_zero e.range).mpr ⟨x, rfl⟩
  have hik : ∀ x : (LinearMap.id : ((n : t) → T n) →ₗ[R] ((n : t) → T n)).ker,
      (1 : R) • x = 0 := by
    intro x
    apply Subtype.ext
    exact (one_smul R (x : (n : t) → T n)).trans x.property
  obtain ⟨hfk, hfc⟩ := ker_coker_annihilated_of_comparison_square f u e LinearMap.id hsq
    (g ^ q) (g ^ q) 1 1 1 huk huc hek hec hik
  exact ⟨q, by simpa only [mul_one] using hfk,
    by simpa only [one_mul, mul_one] using hfc⟩

end SerrePositivity.CLMST
