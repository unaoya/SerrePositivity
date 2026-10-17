module

public import SerrePositivity.CLMST.Prop247RankProductAway
public import SerrePositivity.CommutativeAlgebra.LocalizationPowerBound
public import SerrePositivity.CommutativeAlgebra.ReducedFiniteFreeIsogeny
public import SerrePositivity.HomologicalAlgebra.TwoTermConeAnnihilator

/-! # Prop 2.4.7：元の R→∏Ri の実錐の冪零化

通常の rank 像の有限直積について、局所化同型から元の錐へ戻す。
perfectoid 化後の比較とは区別する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.CLMST
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- 通常の元の rank 像への直積写像の実錐は g の一つの冪で零化される。
核の有限生成性、各 Ri の有限表示性は仮定しない。 -/
theorem prop247_rankImageProduct_cone_isogeny
    (R S : Type u) [CommRing R] [IsReduced R] [CommRing S] [Algebra R S]
    [Module.Finite R S] (g : R)
    (hetale : letI := GenericEtale.awayAlgebra R S g
      Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap R S g)))
    (t : Finset ℕ)
    (ht : ∀ x : PrimeSpectrum.basicOpen g, prop247_awayRank R S g x ∈ t) :
    ∃ q : ℕ, moduleMapConeScalar R
      (prop247_toRankImageProduct R S g hetale t).toLinearMap (g ^ q) = 0 := by
  let P := prop247_rankImageProduct R S g hetale t
  let f := prop247_toRankImageProduct R S g hetale t
  letI : Module.Finite R P := prop247_rankImageProduct_finite R S g hetale t
  have hloc := prop247_toRankImageProduct_away_bijective R S g hetale t ht
  have hk (x : R) (hx : f x = 0) : g • x = 0 := by
    obtain ⟨n, hn⟩ := Localization.awayMap_injective_iff.mp hloc.1 x hx
    exact mul_eq_zero_of_pow_mul_eq_zero g x ⟨n, hn⟩
  have hc : ∃ n : ℕ, ∀ y : P ⧸ f.toLinearMap.range, g ^ n • y = 0 := by
    apply exists_uniform_pow_smul_zero g
    intro y
    obtain ⟨y, rfl⟩ := f.toLinearMap.range.mkQ_surjective y
    obtain ⟨r, n, hr⟩ := Localization.awayMap_surjective_iff.mp hloc.2 y
    refine ⟨n, ?_⟩
    rw [← map_smul]
    apply (Submodule.Quotient.mk_eq_zero f.toLinearMap.range).mpr
    refine ⟨r, ?_⟩
    rw [Algebra.smul_def, map_pow]
    exact hr
  obtain ⟨n, hn⟩ := hc
  refine ⟨1 + n, ?_⟩
  rw [pow_add, pow_one]
  exact moduleMapConeScalar_eq_zero_of_ker_coker_annihilated R f.toLinearMap g (g ^ n) hk hn

end SerrePositivity.CLMST
