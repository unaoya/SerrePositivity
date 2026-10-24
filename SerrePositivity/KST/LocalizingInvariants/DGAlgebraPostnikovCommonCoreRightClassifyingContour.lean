module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightClassifyingZeroSquare
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRectangleOfHom

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
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
open ProExcision
variable (R : Type u) [CommRing R] {n : ℤ} (hn : 0 ≤ n)
  {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (lowerFunctor R n hn)) i m hi)
  (d : PostnikovCommonLayerInverse R hn f c) {j : ℕ} (hj : j ≤ i)

attribute [local instance] PostnikovRoofZeroSpan.refined_source_nonpositive
  PostnikovRoofZeroSpan.refined_target_nonpositive

/-- 元の正方形から構成した、二つの輪郭経路の固定端点二重経路。 -/
def postnikovCommonRightClassifyingContourSquare :
  let N := DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj n) 1
  let H := (postnikovCommonRightClassifyingZeroSquare R hn f c d hj).hom
  let q := postnikovCommonRightClassifyingZeroProjection R hn f c d hj
  let h := postnikovCommonRightClassifyingZeroSquare_projection R hn f c d hj
  let v := SquareZero.RectangleOfHom.outerSource N H q h
  let w := SquareZero.RectangleOfHom.outerTarget N H q h
  let l := SquareZero.RectangleOfHom.innerSource N H q h
  let r := SquareZero.RectangleOfHom.innerTarget N H q h
  SquareZero.RelativeWitnessSquare (v.comp r) (l.comp w) := by
  let N := DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj n) 1
  let H := (postnikovCommonRightClassifyingZeroSquare R hn f c d hj).hom
  let q := postnikovCommonRightClassifyingZeroProjection R hn f c d hj
  let h := postnikovCommonRightClassifyingZeroSquare_projection R hn f c d hj
  exact (SquareZero.RectangleOfHom.rectangle N H q h).contourSquare

/-- 元の四辺の実輸送の二合成を結ぶ乗法的経路。 -/
def postnikovCommonRightClassifyingContourTransportHomotopy :
  let N := DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj n) 1
  let H := (postnikovCommonRightClassifyingZeroSquare R hn f c d hj).hom
  let q := postnikovCommonRightClassifyingZeroProjection R hn f c d hj
  let h := postnikovCommonRightClassifyingZeroSquare_projection R hn f c d hj
  let v := SquareZero.RectangleOfHom.outerSource N H q h
  let w := SquareZero.RectangleOfHom.outerTarget N H q h
  let l := SquareZero.RectangleOfHom.innerSource N H q h
  let r := SquareZero.RectangleOfHom.innerTarget N H q h
  Path.Witness R
    (SquareZeroExtension.transport N v ≫ SquareZeroExtension.transport N r)
    (SquareZeroExtension.transport N l ≫ SquareZeroExtension.transport N w) := by
  let N := DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj n) 1
  let H := (postnikovCommonRightClassifyingZeroSquare R hn f c d hj).hom
  let q := postnikovCommonRightClassifyingZeroProjection R hn f c d hj
  let h := postnikovCommonRightClassifyingZeroSquare_projection R hn f c d hj
  exact SquareZeroExtension.contourTransportHomotopy N
    (SquareZero.RectangleOfHom.rectangle N H q h)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
