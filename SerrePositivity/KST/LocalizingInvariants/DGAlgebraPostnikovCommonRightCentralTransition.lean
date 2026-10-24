module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightGlueTransition
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeWitnessBaseChange

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightCentralTransition
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreSpecialization

/-!
概要：P 上の classifying 正方形の元の中央辺を、B 遷移後の三経路貼合せの中央辺と同定する。
方針：同じ全底経路と、零底 class への全経路射影による一意性を使う。
規約：経路の端点やホモロジーだけの一致ではない。使われ方：Γ 右合成の三経路比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (postnikovFunctor R 1)) i m hi)
  (d : PostnikovCommonLayerInverse R f c) {j : ℕ} (hj : j ≤ i)

lemma postnikovCommonRightClassifyingBaseChangeHom_central :
    postnikovCommonRightClassifyingBaseChangeHom R f c d hj ≫
      Path.source R (Path.algebra R (SquareZero.algebra (postnikovCommonClassBase R f c d)
        (bimoduleRestrict (postnikovCommonRightClassifyingBase R f c d hj)
          (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1)))) =
    (SquareZero.baseChangeRelativeWitness (postnikovCommonRightClassifyingBase R f c d hj)
      (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1)
      (postnikovCommonRightClassifyingProjection R f c d)
      (postnikovCommonRightTransitionOverRelative R f c d hj
        (postnikovCommonRightFixedCentralRelative R f c d))).hom :=
  PostnikovCommonCore.postnikovCommonRightClassifyingBaseChangeHom_central
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
