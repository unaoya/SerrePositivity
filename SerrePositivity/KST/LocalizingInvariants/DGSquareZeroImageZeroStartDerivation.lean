module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroImageZeroStartLift
public import SerrePositivity.KST.LocalizingInvariants.DGDerivationOfMapOver
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPathQuasiIso

/-!
概要：零切断からの実経路で得た像の lift を derivation とし、元の底と準同型比較。
方針：構成した実代数射の底射影を使い、その厳密な底上の derivation を取る。
規約：元の底への比較は実経路で保持。使われ方：LT の底変更前の像 class の供給。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZeroImageFiber.ZeroStart
variable {R : Type u} [CommRing R] {A W : Mon (Complex R)} {M N : Bimod A A} (f : M ⟶ N)
  (a : W ⟶ SquareZero.algebra A N) (b : W ⟶ A)
  (h : DGAlgebra.Path.Witness R (b ≫ zeroSection f) (a ≫ quotient f))

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

lemma derivedBase_quasiIso (hb : QuasiIso b.hom) : QuasiIso (derivedBase f a b h).hom := by
  have hq : QuasiIso (DGAlgebra.cellAugmentation R W ≫ b).hom := by
    change QuasiIso ((DGAlgebra.cellAugmentation R W).hom ≫ b.hom)
    exact quasiIso_comp _ _ (hφ := DGAlgebra.cellAugmentation_quasiIso R W) (hφ' := hb)
  exact (derivedBaseWitness f a b h).quasiIso_iff.mpr hq

def derivedDerivationWitness : DGAlgebra.Path.Witness R
    (((derivedDerivation f a b h).section ≫ SquareZero.mapOver (derivedBase f a b h) _ _
      (𝟙 (bimoduleRestrict (derivedBase f a b h) (DGBimoduleImage.obj f)))) ≫ inclusion f)
    (DGAlgebra.cellAugmentation R W ≫ a) := by
  rw [derivedDerivation_section]
  exact derivedLiftInclusionWitness f a b h

end SerrePositivity.KST.LocalizingInvariants.SquareZeroImageFiber.ZeroStart
