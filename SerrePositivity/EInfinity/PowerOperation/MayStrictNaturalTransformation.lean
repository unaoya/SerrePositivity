module

public import SerrePositivity.EInfinity.PowerOperation.MayPowerZeroAdditivity
public import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# 厳密 BE 代数上の May の P⁰ の自然変換

May, Proposition 2.3(i)(ii)。全整数次数のホモロジー可換群上の演算を、
厳密な BE 代数と全ての代数射について一つの自然変換に束ねる。
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory HomologicalComplex
open SerrePositivity.EInfinity.BarrattEccles
variable (p : ℕ) [Fact p.Prime]

/-- 厳密 BE 代数の全整数次数のホモロジー可換群関手。 -/
def mayStrictHomology (n : ℤ) : (operad (ZMod p)).Algebra ⥤ AddCommGrpCat :=
  Operad.Algebra.forget (operad (ZMod p)) ⋙
    homologyFunctor (ModuleCat (ZMod p)) (.up ℤ) (-n) ⋙
      forget₂ (ModuleCat (ZMod p)) AddCommGrpCat

/-- 指定された May の P⁰ は可換群値関手全体の自然変換。 -/
def mayStrictPowerZero (n : ℤ) : mayStrictHomology p n ⟶ mayStrictHomology p n where
  app X := AddCommGrpCat.ofHom (mayPowerZeroAddHom p X n)
  naturality X Y f := by
    ext x
    exact (mayPowerZeroAddHom_naturality p X f n x).symm

lemma mayStrictPowerZero_app (n : ℤ) (X : (operad (ZMod p)).Algebra)
    (x : X.carrier.homology (-n)) :
    (mayStrictPowerZero p n).app X x = mayPowerZeroHomology p X n x := rfl

end SerrePositivity.EInfinity.PowerOperation
