module

public import SerrePositivity.CLMST.Prop247AicRankImages
public import SerrePositivity.CLMST.Prop247RankBaseChangeDiagram
public import SerrePositivity.CLMST.Prop247RankValuation

/-! # Prop 2.4.7：実 perfectoid rank 係数への付値環写像の一意延長

André 基底上では元の Ri 自身が perfectoid であり、各 Ri→Ti は同型である。
通常の rank 像で証明済みの延長をこの実同型で移す。
付値環自身の perfectoid 性・離散性・rank・完備性は要求しない。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.CLMST
set_option backward.isDefEq.respectTransparency false

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (hAIC : IsAbsolutelyIntegrallyClosed R) (g : R)
    (hetale : letI := GenericEtale.awayAlgebra R S g
      Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap R S g)))
    (t : Finset ℕ) (T : t → Type u)
    [∀ n : t, CommRing (T n)] [∀ n : t, Algebra R (T n)]
    [∀ n : t, Algebra (prop247_rankSourceImage R S g hetale n) (T n)]
    [∀ n : t, IsScalarTower R (prop247_rankSourceImage R S g hetale n) (T n)]
    (hf : ∀ n : t, IsPerfectoidization p
      (algebraMap (prop247_rankSourceImage R S g hetale n) (T n)))

include hR hAIC hf

/-- 各元の普遍単位の直積は、元の R 代数写像そのものとして全単射である。 -/
theorem prop247_aic_rankTargetProductMap_bijective :
    Function.Bijective (prop247_rankTargetProductMap R S g hetale t T) :=
  Function.Bijective.piMap (fun n : t =>
    prop247_aic_rankTarget_unit_bijective R S p hR hAIC g hetale n (T n)
      (algebraMap (prop247_rankSourceImage R S g hetale n) (T n)) (hf n))

/-- 任意の付値環への元の写像は、実 perfectoid rank 係数の有限直積へ一意に延長する。
原典の p 完備 rank 1 付値環を含み、そのような付値環の perfectoid 性は仮定しない。 -/
theorem prop247_aic_rankTargetProduct_valuation_extension
    (ht : ∀ x : PrimeSpectrum.basicOpen g, prop247_awayRank R S g x ∈ t)
    (V : Type v) [CommRing V] [IsDomain V] [ValuationRing V] [Algebra R V]
    (hg : algebraMap R V g ≠ 0) :
    ∃! l : ((n : t) → T n) →+* V,
      l.comp (algebraMap R ((n : t) → T n)) = algebraMap R V := by
  letI := hR.isReduced R p
  let e := AlgEquiv.ofBijective (prop247_rankTargetProductMap R S g hetale t T)
    (prop247_aic_rankTargetProductMap_bijective R S p hR hAIC g hetale t T hf)
  have hsource := prop247_rankImageProduct_valuation_extension R S g hetale t ht V hg
  change ∃! l : prop247_rankImageProduct R S g hetale t →+* V,
    l.comp (algebraMap R (prop247_rankImageProduct R S g hetale t)) = algebraMap R V at hsource
  obtain ⟨l, hl, hu⟩ := hsource
  refine ⟨l.comp e.symm.toRingHom, ?_, ?_⟩
  · change (l.comp e.symm.toRingHom).comp (algebraMap R ((n : t) → T n)) = algebraMap R V
    apply RingHom.ext
    intro r
    change l (e.symm (algebraMap R ((n : t) → T n) r)) = algebraMap R V r
    rw [e.symm.commutes]
    exact RingHom.congr_fun hl r
  · intro m hm
    have hm' : (m.comp e.toRingHom).comp
        (algebraMap R (prop247_rankImageProduct R S g hetale t)) = algebraMap R V := by
      apply RingHom.ext
      intro r
      change m (e (algebraMap R (prop247_rankImageProduct R S g hetale t) r)) = algebraMap R V r
      rw [e.commutes]
      exact RingHom.congr_fun hm r
    have h := hu (m.comp e.toRingHom) hm'
    apply RingHom.ext
    intro y
    change m y = l (e.symm y)
    have hy := RingHom.congr_fun h (e.symm y)
    change m (e (e.symm y)) = l (e.symm y) at hy
    simpa only [e.apply_symm_apply] using hy

end SerrePositivity.CLMST
