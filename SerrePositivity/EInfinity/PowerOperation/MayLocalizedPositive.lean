module

public import SerrePositivity.EInfinity.PowerOperation.MayLocalizedPowerZero

/-!
# ho(CAlg F_p) 上の P⁰ の正次数での消滅

May, Definition 2.2・Proposition 2.3。負の添字の D_i を零とする同じ規約を、
全厳密代数からの通常の局所化を通して運ぶ。
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory SSet
open SerrePositivity.EInfinity.BarrattEccles

lemma mayStrictPowerZero_pos (p : ℕ) [Fact p.Prime] (n : ℤ) (hn : 0 < n) :
    mayStrictPowerZero p n = 0 := by
  ext X x
  exact mayPowerZeroHomology_pos p X n hn x

/-- 正次数の全成分は零。局所化した全関手の自然変換としての等式。 -/
lemma mayLocalizedPowerZero_pos (p : ℕ) [Fact p.Prime] (n : ℤ) (hn : 0 < n) :
    mayLocalizedPowerZero p n = 0 := by
  let _ := ordinaryAlgebraHoSource_isLocalization (ZMod p)
  apply (Localization.fullyFaithfulWhiskeringLeft (ordinaryAlgebraHoSource (ZMod p))
    (ordinaryAlgebraWeak (ZMod p)) AddCommGrpCat).map_injective
  change Functor.whiskerLeft (ordinaryAlgebraHoSource (ZMod p))
    (mayLocalizedPowerZero p n) =
      Functor.whiskerLeft (ordinaryAlgebraHoSource (ZMod p)) 0
  rw [mayLocalizedPowerZero_source, mayStrictPowerZero_pos p n hn]
  simp only [Limits.comp_zero, Limits.zero_comp]
  rfl

end SerrePositivity.EInfinity.PowerOperation
