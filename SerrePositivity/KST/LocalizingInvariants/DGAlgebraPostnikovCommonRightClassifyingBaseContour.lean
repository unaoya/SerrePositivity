module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightClassifyingBaseChange

/-!
概要：元の共通底 P 上で、指定右経路の classifying 正方形の輪郭比較を構成する。
方針：全二重経路の底変更後に四辺を相対化し、固定端点補正と実輸送を適用する。
規約：元の共通底と cell 射影を保持する。使われ方：新 Γ の元の右三角形。
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

/-- 同じ元の P 上で、輪郭二経路を結ぶ固定端点二重経路。 -/
def postnikovCommonRightClassifyingBaseContourSquare :
  let N := bimoduleRestrict (postnikovCommonRightClassifyingBase R f c d hj)
    (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1)
  let H := postnikovCommonRightClassifyingBaseChangeHom R f c d hj
  let q := postnikovCommonRightClassifyingProjection R f c d
  let h := postnikovCommonRightClassifyingBaseChangeHom_projection R f c d hj
  let v := SquareZero.RectangleOfHom.outerSource N H q h
  let w := SquareZero.RectangleOfHom.outerTarget N H q h
  let l := SquareZero.RectangleOfHom.innerSource N H q h
  let r := SquareZero.RectangleOfHom.innerTarget N H q h
  SquareZero.RelativeWitnessSquare (v.comp r) (l.comp w) := by
  let N := bimoduleRestrict (postnikovCommonRightClassifyingBase R f c d hj)
    (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1)
  let H := postnikovCommonRightClassifyingBaseChangeHom R f c d hj
  let q := postnikovCommonRightClassifyingProjection R f c d
  let h := postnikovCommonRightClassifyingBaseChangeHom_projection R f c d hj
  exact (SquareZero.RectangleOfHom.rectangle N H q h).contourSquare

/-- 元の P 上の相対模型で、輪郭の二つの実輸送合成を結ぶ経路。 -/
def postnikovCommonRightClassifyingBaseContourTransportHomotopy :
  let N := bimoduleRestrict (postnikovCommonRightClassifyingBase R f c d hj)
    (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1)
  let H := postnikovCommonRightClassifyingBaseChangeHom R f c d hj
  let q := postnikovCommonRightClassifyingProjection R f c d
  let h := postnikovCommonRightClassifyingBaseChangeHom_projection R f c d hj
  let v := SquareZero.RectangleOfHom.outerSource N H q h
  let w := SquareZero.RectangleOfHom.outerTarget N H q h
  let l := SquareZero.RectangleOfHom.innerSource N H q h
  let r := SquareZero.RectangleOfHom.innerTarget N H q h
  Path.Witness R
    (SquareZeroExtension.transport N v ≫ SquareZeroExtension.transport N r)
    (SquareZeroExtension.transport N l ≫ SquareZeroExtension.transport N w) := by
  let N := bimoduleRestrict (postnikovCommonRightClassifyingBase R f c d hj)
    (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1)
  let H := postnikovCommonRightClassifyingBaseChangeHom R f c d hj
  let q := postnikovCommonRightClassifyingProjection R f c d
  let h := postnikovCommonRightClassifyingBaseChangeHom_projection R f c d hj
  exact SquareZeroExtension.contourTransportHomotopy N
    (SquareZero.RectangleOfHom.rectangle N H q h)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
