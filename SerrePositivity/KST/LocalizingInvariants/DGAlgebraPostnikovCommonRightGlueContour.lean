module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightBaseGlue
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRectangleTopGlue

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightGlueContour
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreSpecialization

/-!
概要：元の三経路貼合せを B 遷移で移した後、P 上の classifying 輪郭比較へ接続する。
方針：元の中央辺と全貼合せの厳密同定を使い、両側の元の経路を輪郭に取り付ける。
規約：実二重経路も実輸送経路も構成する。使われ方：Γ の右合成の実貼合せ計算。
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

/-- 元の B 遷移後の全貼合せ G を保持する、P 上の輪郭二重経路。 -/
def postnikovCommonRightGlueContourSquare :
  let N := bimoduleRestrict (postnikovCommonRightClassifyingBase R f c d hj)
    (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1)
  let H := postnikovCommonRightClassifyingBaseChangeHom R f c d hj
  let p := postnikovCommonRightClassifyingProjection R f c d
  let hbase := postnikovCommonRightClassifyingBaseChangeHom_projection R f c d hj
  let V := postnikovCommonRightTransitionLift R f c d hj
    (postnikovCommonRightFixedCentralRelative R f c d)
  let T := postnikovCommonRightTransitionLift R f c d hj
    (postnikovCommonRightFixedTargetRelative R f c d)
  let S := postnikovCommonRightTransitionLift R f c d hj
    (postnikovCommonRightFixedSourceRelative R f c d)
  let G := postnikovCommonRightTransitionLift R f c d hj
    (postnikovCommonRightAffineFixedGlue R f c d)
  let hTop := postnikovCommonRightClassifyingBaseChangeHom_central R f c d hj
  let T' := SquareZero.RectangleOfHom.towardTopSource N H p V hTop T
  let S' := SquareZero.RectangleOfHom.towardTopTarget N H p V hTop S
  let r := SquareZero.RectangleOfHom.innerTarget N H p hbase
  let l := SquareZero.RectangleOfHom.innerSource N H p hbase
  let w := SquareZero.RectangleOfHom.outerTarget N H p hbase
  SquareZero.RelativeWitnessSquare (G.comp (S'.comp r)) (T'.comp (l.comp w)) :=
  PostnikovCommonCore.postnikovCommonRightGlueContourSquare
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

/-- 同じ元の G と両側の経路を使う、実相対模型の輸送合成の経路。 -/
def postnikovCommonRightGlueContourTransportHomotopy :
  let N := bimoduleRestrict (postnikovCommonRightClassifyingBase R f c d hj)
    (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1)
  let H := postnikovCommonRightClassifyingBaseChangeHom R f c d hj
  let p := postnikovCommonRightClassifyingProjection R f c d
  let hbase := postnikovCommonRightClassifyingBaseChangeHom_projection R f c d hj
  let V := postnikovCommonRightTransitionLift R f c d hj
    (postnikovCommonRightFixedCentralRelative R f c d)
  let T := postnikovCommonRightTransitionLift R f c d hj
    (postnikovCommonRightFixedTargetRelative R f c d)
  let S := postnikovCommonRightTransitionLift R f c d hj
    (postnikovCommonRightFixedSourceRelative R f c d)
  let G := postnikovCommonRightTransitionLift R f c d hj
    (postnikovCommonRightAffineFixedGlue R f c d)
  let hTop := postnikovCommonRightClassifyingBaseChangeHom_central R f c d hj
  let T' := SquareZero.RectangleOfHom.towardTopSource N H p V hTop T
  let S' := SquareZero.RectangleOfHom.towardTopTarget N H p V hTop S
  let r := SquareZero.RectangleOfHom.innerTarget N H p hbase
  let l := SquareZero.RectangleOfHom.innerSource N H p hbase
  let w := SquareZero.RectangleOfHom.outerTarget N H p hbase
  Path.Witness R
    (SquareZeroExtension.transport N G ≫
      (SquareZeroExtension.transport N S' ≫ SquareZeroExtension.transport N r))
    (SquareZeroExtension.transport N T' ≫
      (SquareZeroExtension.transport N l ≫ SquareZeroExtension.transport N w)) :=
  PostnikovCommonCore.postnikovCommonRightGlueContourTransportHomotopy
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
