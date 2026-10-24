module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCore
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovShiftedLayer
public import SerrePositivity.KST.LocalizingInvariants.DGBimoduleShiftRestrictedMap

/-!
概要：任意の切断次数の共通核の係数射を、独立な整数 shift へ移す。
方針：元の分母・分子による制限を固定し、検証済みの shift 制限射を使う。
規約：class 整合の経路は未主張。使われ方：拡大代数の逆の持ち上げ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
open ProExcision
variable (R : Type u) [CommRing R] {n : ℤ} (hn : 0 ≤ n)
  {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (postnikovFunctor R n)) i m hi)

abbrev shiftedDenominatorLayer (s : ℤ) : Bimod c.roof.apex c.roof.apex :=
  bimoduleRestrict c.roof.denominator (postnikovShiftedLayerBimodule R (B.obj m).obj n hn s)

abbrev shiftedNumeratorLayer (s : ℤ) : Bimod c.roof.apex c.roof.apex :=
  bimoduleRestrict c.roof.numerator (postnikovShiftedLayerBimodule R (A.obj i).obj n hn s)

variable (u : denominatorLayer R hn f c ⟶ numeratorLayer R hn f c) (s : ℤ)

abbrev shiftedCoefficientMap :
    shiftedDenominatorLayer R hn f c s ⟶
      shiftedNumeratorLayer R hn f
        c s :=
  DGBimoduleShift.restrictedMap _ _ _ _ s u

lemma shiftedCoefficientMap_hom :
    (shiftedCoefficientMap R hn f c u s).hom = u.hom⟦s⟧' :=
  DGBimoduleShift.restrictedMap_hom _ _ _ _ s u


end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
