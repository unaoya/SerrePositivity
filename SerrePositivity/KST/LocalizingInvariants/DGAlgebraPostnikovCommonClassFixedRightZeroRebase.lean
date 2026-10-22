module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonClassFixedBaseNormalization

/-!
概要：元の native 右 class 二重経路を、元の classifying 底射の表示に揃える。
方針：P 全体上の底射の等式を Γ 射影で前合成し、元の全二重経路を移す。
規約：native 合成と分母経路の全射を変更しない。使われ方：元の P への底変更 lift。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (postnikovFunctor R 1)) i m hi)
  (d : PostnikovCommonLayerInverse R f c) {j : ℕ} (hj : j ≤ i)
  (e : PostnikovZeroLayerInverse R 1 f j i hj)

def postnikovCommonClassFixedRightDenominatorZero :=
  (postnikovCommonClassFixedRightDenominatorPath R f c d hj e).rebase
    (postnikovCommonClassFixedZeroBase_projection R f c d hj)

def postnikovCommonClassFixedRightCompletedZero :=
  (postnikovCommonClassFixedRightCompletedPath R f c d hj e).rebase
    (postnikovCommonClassFixedZeroBase_projection R f c d hj)

def postnikovCommonClassFixedRightRebasedZeroSquare : SquareZero.RelativeWitnessSquare
    (postnikovCommonClassFixedRightDenominatorZero R f c d hj e)
    (postnikovCommonClassFixedRightCompletedZero R f c d hj e) :=
  (postnikovCommonClassFixedRightZeroSquare R f c d hj e).rebase
    (postnikovCommonClassFixedZeroBase_projection R f c d hj)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
