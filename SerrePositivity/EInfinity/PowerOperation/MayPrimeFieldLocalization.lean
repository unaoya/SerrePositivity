module

public import SerrePositivity.EInfinity.PowerOperation.MayNormalizedSourceComparison
public import Mathlib.Algebra.Field.ULift

/-!
# 任意の宇宙に置いた F_p の上の May の P⁰

May, Definition 2.2・Proposition 2.3。界面と同じ宇宙に置くため F_p を ULift する。
演算の本欄はこの素体だけに置き、ν の像で規格化した同じ D_i を局所化する。
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open SerrePositivity.EInfinity.BarrattEccles

/-- 界面と同じ宇宙に置いた素体。環は F_p そのものの持ち上げ。 -/
abbrev MayPrimeField (p : ℕ) := ULift.{u} (ZMod p)

abbrev mayPrimeFieldHomology (p : ℕ) [Fact p.Prime] (n : ℤ) :=
  hoMap (cAlgForgetDerived (MayPrimeField.{u} p)) ⋙
    additiveCohomologyOnHo (MayPrimeField.{u} p) (-n)

/-- 持ち上げた素体の全 ho(CAlg) 射に自然な、規格化した May の P⁰。 -/
def mayPrimeFieldPowerZero (p : ℕ) [Fact p.Prime] (n : ℤ) :
    mayPrimeFieldHomology.{u} p n ⟶ mayPrimeFieldHomology.{u} p n := by
  let k := MayPrimeField.{u} p
  let L := ordinaryAlgebraHoSource k
  let W := ordinaryAlgebraWeak k
  letI := ordinaryAlgebraHoSource_isLocalization k
  let e := mayNormalizedHomologySourceIso k n
  let c : k := ULift.up (mayNu p n : ZMod p)
  exact (Localization.fullyFaithfulWhiskeringLeft L W AddCommGrpCat).preimage
    (e.hom ≫ mayNormalizedStrictPowerZero p n c ≫ e.inv)

lemma mayPrimeFieldPowerZero_source (p : ℕ) [Fact p.Prime] (n : ℤ) :
    Functor.whiskerLeft (ordinaryAlgebraHoSource (MayPrimeField.{u} p))
      (mayPrimeFieldPowerZero p n) =
      (mayNormalizedHomologySourceIso (MayPrimeField.{u} p) n).hom ≫
        mayNormalizedStrictPowerZero p n (ULift.up (mayNu p n : ZMod p)) ≫
          (mayNormalizedHomologySourceIso (MayPrimeField.{u} p) n).inv := by
  let _ := ordinaryAlgebraHoSource_isLocalization (MayPrimeField.{u} p)
  exact (Localization.fullyFaithfulWhiskeringLeft
    (ordinaryAlgebraHoSource (MayPrimeField.{u} p)) (ordinaryAlgebraWeak (MayPrimeField.{u} p))
      AddCommGrpCat).map_preimage _

end SerrePositivity.EInfinity.PowerOperation
