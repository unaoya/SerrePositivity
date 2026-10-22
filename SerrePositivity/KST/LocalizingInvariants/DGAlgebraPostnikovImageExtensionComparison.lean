module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovImageExtension
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraHomotopyPullbackPathComparison

/-!
概要：像拡大からの実模型射を、元の class の実準同型 zigzag へ接続する。
方針：元の包含比較経路を mapping-path で厳密化し、元の augmentation を使う。
規約：各比較は右脚を厳密に保持。使われ方：元の隣接 Postnikov 拡大との比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] {B C : Mon (Complex R)}
  [B.X.IsStrictlyLE 0] [C.X.IsStrictlyLE 0] (f : B ⟶ C) (n : ℤ) (hn : 0 ≤ n)

abbrev imageOriginalAugmentation :=
  cellAugmentation R (cellResolution R (cellResolution R (postnikov R B n)))

abbrev postnikovImagePathExtension := HomotopyPullbackModel.algebra R
  (MappingPath.target R (postnikovImageClass R f n hn ≫ postnikovImageClassTargetMap R f n hn))
  (SquareZero.zeroSection (postnikov R C n) (postnikovShiftedLayerBimodule R C n hn 1))

abbrev postnikovImageComposedExtension := HomotopyPullbackModel.algebra R
  (imageOriginalAugmentation R (B := B) n ≫ classCommonTarget R f n hn)
  (SquareZero.zeroSection (postnikov R C n) (postnikovShiftedLayerBimodule R C n hn 1))

abbrev postnikovCommonExtension := HomotopyPullbackModel.algebra R (classCommonTarget R f n hn)
  (SquareZero.zeroSection (postnikov R C n) (postnikovShiftedLayerBimodule R C n hn 1))

def postnikovImageIncludedToPath : postnikovImageIncludedExtension R f n hn ⟶
    postnikovImagePathExtension R f n hn := PathCospanComparison.originalToPath R _ _

def postnikovImageComposedToPath : postnikovImageComposedExtension R f n hn ⟶
    postnikovImagePathExtension R f n hn :=
  PathCospanComparison.composedToPath R _ _ _ _ (postnikovImageOriginalClassWitness R f n hn)

def postnikovImageComposedToCommon : postnikovImageComposedExtension R f n hn ⟶
    postnikovCommonExtension R f n hn := PathCospanComparison.composedToOriginal R _ _ _

lemma postnikovImageIncludedToPath_quasiIso :
    QuasiIso (postnikovImageIncludedToPath R f n hn).hom :=
  PathCospanComparison.originalToPath_quasiIso R _ _

lemma postnikovImageComposedToPath_quasiIso :
    QuasiIso (postnikovImageComposedToPath R f n hn).hom :=
  PathCospanComparison.composedToPath_quasiIso R _ _ _ _
    (postnikovImageOriginalClassWitness R f n hn)

lemma postnikovImageComposedToCommon_quasiIso :
    QuasiIso (postnikovImageComposedToCommon R f n hn).hom :=
  PathCospanComparison.composedToOriginal_quasiIso R _ _ _ (cellAugmentation_quasiIso R _)

lemma postnikovImageIncludedToPath_right : postnikovImageIncludedToPath R f n hn ≫
    HomotopyPullbackModel.right R _ _ = HomotopyPullbackModel.right R _ _ :=
  PathCospanComparison.originalToPath_right R _ _

lemma postnikovImageComposedToPath_right : postnikovImageComposedToPath R f n hn ≫
    HomotopyPullbackModel.right R _ _ = HomotopyPullbackModel.right R _ _ :=
  PathCospanComparison.composedToPath_right R _ _ _ _ (postnikovImageOriginalClassWitness R f n hn)

lemma postnikovImageComposedToCommon_right : postnikovImageComposedToCommon R f n hn ≫
    HomotopyPullbackModel.right R _ _ = HomotopyPullbackModel.right R _ _ :=
  PathCospanComparison.composedToOriginal_right R _ _ _

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
