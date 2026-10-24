module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightClassifyingZeroSquare
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRectangleOfHom

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightClassifyingContour
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreSpecialization

/-!
概要：元の指定右経路と B 遷移の classifying 正方形から、輪郭の実輸送比較を構成する。
方針：零底で証明した全射影から四辺を相対化し、connection による補正を適用する。
規約：二重経路の存在を追加仮定にしない。使われ方：新 Γ の右合成比較への接続。
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

/-- 元の正方形から構成した、二つの輪郭経路の固定端点二重経路。 -/
def postnikovCommonRightClassifyingContourSquare :
  let N := DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1
  let H := (postnikovCommonRightClassifyingZeroSquare R f c d hj).hom
  let q := postnikovCommonRightClassifyingZeroProjection R f c d hj
  let h := postnikovCommonRightClassifyingZeroSquare_projection R f c d hj
  let v := SquareZero.RectangleOfHom.outerSource N H q h
  let w := SquareZero.RectangleOfHom.outerTarget N H q h
  let l := SquareZero.RectangleOfHom.innerSource N H q h
  let r := SquareZero.RectangleOfHom.innerTarget N H q h
  SquareZero.RelativeWitnessSquare (v.comp r) (l.comp w) :=
  PostnikovCommonCore.postnikovCommonRightClassifyingContourSquare
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

/-- 元の四辺の実輸送の二合成を結ぶ乗法的経路。 -/
def postnikovCommonRightClassifyingContourTransportHomotopy :
  let N := DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1
  let H := (postnikovCommonRightClassifyingZeroSquare R f c d hj).hom
  let q := postnikovCommonRightClassifyingZeroProjection R f c d hj
  let h := postnikovCommonRightClassifyingZeroSquare_projection R f c d hj
  let v := SquareZero.RectangleOfHom.outerSource N H q h
  let w := SquareZero.RectangleOfHom.outerTarget N H q h
  let l := SquareZero.RectangleOfHom.innerSource N H q h
  let r := SquareZero.RectangleOfHom.innerTarget N H q h
  Path.Witness R
    (SquareZeroExtension.transport N v ≫ SquareZeroExtension.transport N r)
    (SquareZeroExtension.transport N l ≫ SquareZeroExtension.transport N w) :=
  PostnikovCommonCore.postnikovCommonRightClassifyingContourTransportHomotopy
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
