module

public import SerrePositivity.CLMST.Prop247RankProductAway
public import SerrePositivity.CommutativeAlgebra.IntegralAwayExtension
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-! # Prop 2.4.7：元の rank 像の有限直積への付値環写像の一意延長

原典の Ri の実データ・有限性・局所化同型を使う。
perfectoid 化した有限直積への延長や excision はここでは主張しない。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.CLMST
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- 元の R→∏Ri は、g を零にしない任意の付値環への写像の一意延長を与える。
終域の離散性・rank・完備性は追加しない。 -/
theorem prop247_rankImageProduct_valuation_extension
    (R S : Type u) [CommRing R] [IsReduced R] [CommRing S] [Algebra R S]
    [Module.Finite R S] (g : R)
    (hetale : letI := GenericEtale.awayAlgebra R S g
      Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap R S g)))
    (t : Finset ℕ)
    (ht : ∀ x : PrimeSpectrum.basicOpen g, prop247_awayRank R S g x ∈ t)
    (V : Type v) [CommRing V] [IsDomain V] [ValuationRing V] [Algebra R V]
    (hg : algebraMap R V g ≠ 0) :
    ∃! l : prop247_rankImageProduct R S g hetale t →+* V,
      l.comp (prop247_toRankImageProduct R S g hetale t).toRingHom = algebraMap R V := by
  letI := prop247_rankImageProduct_finite R S g hetale t
  have hiso := prop247_toRankImageProduct_away_bijective R S g hetale t ht
  change ∃! l : prop247_rankImageProduct R S g hetale t →+* V,
    l.comp (algebraMap R (prop247_rankImageProduct R S g hetale t)) = algebraMap R V
  exact existsUnique_valuation_extension_of_integral_away_bijective R
    (prop247_rankImageProduct R S g hetale t) V g hg hiso

end SerrePositivity.CLMST
