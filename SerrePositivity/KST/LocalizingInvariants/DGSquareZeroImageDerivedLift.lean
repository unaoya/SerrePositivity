module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroImageHomotopyFiber
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraCellQuasiIsoLift

/-!
概要：係数商で零切断へ向かう実乗法的経路から、像の平方零代数への導来 lift を作る。
方針：実経路模型へ持ち上げ、構成した準同型比較を cell 上で経路付きで逆向きに使う。
規約：包含・底射影との比較は実経路。厳密な底の固定は未主張。使われ方：LT の像制限。
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

def modelLift : W ⟶ model f := DGAlgebra.HomotopyPullbackModel.lift R _ _ a b h

def derivedLift : DGAlgebra.cellResolution R W ⟶ SquareZero.algebra A (DGBimoduleImage.obj f) :=
  DGAlgebra.cellQuasiIsoLift R (comparison f) (comparison_quasiIso f) (modelLift f a b h)

def derivedLiftWitness : DGAlgebra.Path.Witness R (derivedLift f a b h ≫ comparison f)
    (DGAlgebra.cellAugmentation R W ≫ modelLift f a b h) :=
  DGAlgebra.cellQuasiIsoLiftWitness R _ _ _

def derivedLiftInclusionWitness : DGAlgebra.Path.Witness R (derivedLift f a b h ≫ inclusion f)
    (DGAlgebra.cellAugmentation R W ≫ a) where
  hom := ((derivedLiftWitness f a b h).postcomp
    (DGAlgebra.HomotopyPullbackModel.left R _ _)).hom
  source_eq := by
    rw [((derivedLiftWitness f a b h).postcomp
      (DGAlgebra.HomotopyPullbackModel.left R _ _)).source_eq, Category.assoc, comparison_left]
  target_eq := by
    rw [((derivedLiftWitness f a b h).postcomp
      (DGAlgebra.HomotopyPullbackModel.left R _ _)).target_eq, Category.assoc]
    exact congrArg (fun q => DGAlgebra.cellAugmentation R W ≫ q)
      (DGAlgebra.HomotopyPullbackModel.lift_left R _ _ _ _ _)

def derivedLiftProjectionWitness : DGAlgebra.Path.Witness R (derivedLift f a b h ≫ projection f)
    (DGAlgebra.cellAugmentation R W ≫ b) where
  hom := ((derivedLiftWitness f a b h).postcomp
    (DGAlgebra.HomotopyPullbackModel.right R _ _)).hom
  source_eq := by
    rw [((derivedLiftWitness f a b h).postcomp
      (DGAlgebra.HomotopyPullbackModel.right R _ _)).source_eq, Category.assoc, comparison_right]
  target_eq := by
    rw [((derivedLiftWitness f a b h).postcomp
      (DGAlgebra.HomotopyPullbackModel.right R _ _)).target_eq, Category.assoc]
    exact congrArg (fun q => DGAlgebra.cellAugmentation R W ≫ q)
      (DGAlgebra.HomotopyPullbackModel.lift_right R _ _ _ _ _)

end SerrePositivity.KST.LocalizingInvariants.SquareZeroImageFiber
