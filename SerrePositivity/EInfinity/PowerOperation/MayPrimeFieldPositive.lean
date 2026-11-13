module

public import SerrePositivity.EInfinity.PowerOperation.MayPrimeFieldLocalization

/-!
# 持ち上げた素体上の May の P⁰ の正次数消滅

May, Definition 2.2・Proposition 2.3。規格化と局所化を通しても、
負の添字の D_i を零とする同じ規約から正次数の消滅を得る。
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory SSet
open SerrePositivity.EInfinity.BarrattEccles

lemma mayNormalizedStrictPowerZero_pos {k : Type u} [CommRing k]
    (p : ℕ) [Fact p.Prime] [CharP k p] (n : ℤ) (hn : 0 < n) (c : k) :
    mayNormalizedStrictPowerZero p n c = 0 := by
  ext X x
  change mayNormalizedHomology p X n c x = 0
  unfold mayNormalizedHomology mayNormalizedClass
  exact dite_eq_right (not_le.mpr (mayZeroIndex_negative p hn))

/-- 界面の宇宙に置いた F_p の上でも、正次数の同じ P⁰ は自然変換全体として零。 -/
lemma mayPrimeFieldPowerZero_pos (p : ℕ) [Fact p.Prime] (n : ℤ) (hn : 0 < n) :
    mayPrimeFieldPowerZero.{u} p n = 0 := by
  let _ := ordinaryAlgebraHoSource_isLocalization (MayPrimeField.{u} p)
  apply (Localization.fullyFaithfulWhiskeringLeft
    (ordinaryAlgebraHoSource (MayPrimeField.{u} p)) (ordinaryAlgebraWeak (MayPrimeField.{u} p))
      AddCommGrpCat).map_injective
  change Functor.whiskerLeft (ordinaryAlgebraHoSource (MayPrimeField.{u} p))
    (mayPrimeFieldPowerZero p n) =
      Functor.whiskerLeft (ordinaryAlgebraHoSource (MayPrimeField.{u} p)) 0
  rw [mayPrimeFieldPowerZero_source, mayNormalizedStrictPowerZero_pos p n hn]
  simp only [Limits.comp_zero, Limits.zero_comp]
  rfl

end SerrePositivity.EInfinity.PowerOperation
