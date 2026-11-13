module

public import SerrePositivity.EInfinity.PowerOperation.MayHomologySourceComparison

/-!
# ho(CAlg F_p) 上の May の P⁰

May, Proposition 2.3(i)(ii)。通常の局所化の充満忠実性により、
全厳密 BE 射に自然なホモロジー演算を ho(CAlg F_p) の全射へ降ろす。
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open SerrePositivity.EInfinity.BarrattEccles

/-- 忘却した導来複体の全整数次数のホモロジー可換群関手。 -/
abbrev mayLocalizedHomology (p : ℕ) [Fact p.Prime] (n : ℤ) :=
  hoMap (cAlgForgetDerived (ZMod p)) ⋙ additiveCohomologyOnHo (ZMod p) (-n)

/-- May の同じ P⁰ を ho(CAlg F_p) の全射に自然な演算へ降ろしたもの。 -/
def mayLocalizedPowerZero (p : ℕ) [Fact p.Prime] (n : ℤ) :
    mayLocalizedHomology p n ⟶ mayLocalizedHomology p n := by
  let L := ordinaryAlgebraHoSource (ZMod p)
  let W := ordinaryAlgebraWeak (ZMod p)
  letI := ordinaryAlgebraHoSource_isLocalization (ZMod p)
  let e := mayHomologySourceIso p n
  exact (Localization.fullyFaithfulWhiskeringLeft L W AddCommGrpCat).preimage
    (e.hom ≫ mayStrictPowerZero p n ≫ e.inv)

/-- 局所化した演算は、同じ指定された厳密な May 演算を回復する。 -/
lemma mayLocalizedPowerZero_source (p : ℕ) [Fact p.Prime] (n : ℤ) :
    Functor.whiskerLeft (ordinaryAlgebraHoSource (ZMod p)) (mayLocalizedPowerZero p n) =
      (mayHomologySourceIso p n).hom ≫ mayStrictPowerZero p n ≫
        (mayHomologySourceIso p n).inv := by
  let _ := ordinaryAlgebraHoSource_isLocalization (ZMod p)
  exact (Localization.fullyFaithfulWhiskeringLeft (ordinaryAlgebraHoSource (ZMod p))
    (ordinaryAlgebraWeak (ZMod p)) AddCommGrpCat).map_preimage _

end SerrePositivity.EInfinity.PowerOperation
