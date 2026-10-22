module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroImageDerivedLift
public import SerrePositivity.KST.LocalizingInvariants.DGDerivationOfMapOver

/-!
概要：実乗法的零経路から得た像への導来 lift を、実 derivation として回収する。
方針：構成した実代数射の底射影を使い、その厳密な底上の derivation を取る。
規約：元の底への比較は実経路で保持。使われ方：LT の底変更前の像 class の供給。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZeroImageFiber
variable {R : Type u} [CommRing R] {A W : Mon (Complex R)} {M N : Bimod A A} (f : M ⟶ N)
  (a : W ⟶ SquareZero.algebra A N) (b : W ⟶ A)
  (h : DGAlgebra.Path.Witness R (a ≫ quotient f) (b ≫ zeroSection f))

def derivedBase : DGAlgebra.cellResolution R W ⟶ A := derivedLift f a b h ≫ projection f

def derivedDerivation : SquareZero.Derivation (DGAlgebra.cellResolution R W)
    (bimoduleRestrict (derivedBase f a b h) (DGBimoduleImage.obj f)) :=
  SquareZero.derivationOfMapOver (derivedBase f a b h) (DGBimoduleImage.obj f)
    (derivedLift f a b h) rfl

lemma derivedDerivation_section : (derivedDerivation f a b h).section ≫
    SquareZero.mapOver (derivedBase f a b h) _ _
      (𝟙 (bimoduleRestrict (derivedBase f a b h) (DGBimoduleImage.obj f))) =
        derivedLift f a b h := SquareZero.derivationOfMapOver_section _ _ _ _

def derivedBaseWitness : DGAlgebra.Path.Witness R (derivedBase f a b h)
    (DGAlgebra.cellAugmentation R W ≫ b) := derivedLiftProjectionWitness f a b h

def derivedDerivationWitness : DGAlgebra.Path.Witness R
    (((derivedDerivation f a b h).section ≫ SquareZero.mapOver (derivedBase f a b h) _ _
      (𝟙 (bimoduleRestrict (derivedBase f a b h) (DGBimoduleImage.obj f)))) ≫ inclusion f)
    (DGAlgebra.cellAugmentation R W ≫ a) := by
  rw [derivedDerivation_section]
  exact derivedLiftInclusionWitness f a b h

end SerrePositivity.KST.LocalizingInvariants.SquareZeroImageFiber
