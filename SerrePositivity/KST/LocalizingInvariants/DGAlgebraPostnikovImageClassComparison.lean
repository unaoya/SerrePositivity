module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovImageClass

/-!
概要：像への実 class と、元の標的 Postnikov class の実乗法的経路を供給する。
方針：構成済みの包含比較経路を元の底変更射で後合成し、元の cell class を回収する。
規約：元の全ての augmentation と係数包含を保持。使われ方：像拡大と隣接拡大の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] {B C : Mon (Complex R)}
  [B.X.IsStrictlyLE 0] [C.X.IsStrictlyLE 0] (f : B ⟶ C) (n : ℤ) (hn : 0 ≤ n)

def postnikovImageClassTargetMap :
    SquareZero.algebra (postnikov R B n) (postnikovShiftedLayerImage R f n hn 1) ⟶
      postnikovDerivationTarget R C n hn :=
  SquareZero.mapOver (postnikovMap R f n) (postnikovShiftedLayerImage R f n hn 1)
    (postnikovShiftedLayerBimodule R C n hn 1) (postnikovShiftedLayerImageInclusion R f n hn 1)

def postnikovImageOriginalClassWitness : Path.Witness R
    (postnikovImageClass R f n hn ≫ postnikovImageClassTargetMap R f n hn)
    (cellAugmentation R (cellResolution R (cellResolution R (postnikov R B n))) ≫
      classCommonTarget R f n hn) where
  hom := ((postnikovImageClassWitness R f n hn).postcomp
    (SquareZero.baseChangeMap (postnikovMap R f n) (postnikovShiftedLayerBimodule R C n hn 1))).hom
  source_eq := by
    have hw := ((postnikovImageClassWitness R f n hn).postcomp
      (SquareZero.baseChangeMap (postnikovMap R f n)
        (postnikovShiftedLayerBimodule R C n hn 1))).source_eq
    exact hw.trans ((Category.assoc _ _ _).trans (congrArg
      (fun q => postnikovImageClass R f n hn ≫ q)
      (SquareZero.coefficientMap_baseChangeMap (postnikovMap R f n)
        (postnikovShiftedLayerImage R f n hn 1) (postnikovShiftedLayerBimodule R C n hn 1)
        (postnikovShiftedLayerImageInclusion R f n hn 1))))
  target_eq := by
    have hw := ((postnikovImageClassWitness R f n hn).postcomp
      (SquareZero.baseChangeMap (postnikovMap R f n)
        (postnikovShiftedLayerBimodule R C n hn 1))).target_eq
    exact hw.trans ((Category.assoc _ _ _).trans (congrArg (fun q =>
      cellAugmentation R (cellResolution R (cellResolution R (postnikov R B n))) ≫ q)
      (SquareZero.baseChangeLift_map _ _ _ _ _)))

def postnikovImageTargetBaseWitness : Path.Witness R
    (postnikovImageBase R f n hn ≫ postnikovMap R f n)
    ((cellAugmentation R (cellResolution R (cellResolution R (postnikov R B n))) ≫
      classCommonBase R (B := B) n) ≫ postnikovMap R f n) :=
  (postnikovImageBaseWitness R f n hn).postcomp (postnikovMap R f n)

lemma postnikovImageCoefficient_upperBound :
    (bimoduleRestrict (postnikovImageBase R f n hn)
      (postnikovShiftedLayerImage R f n hn 1)).X.IsStrictlyLE (-(n + 1) - 1) :=
  postnikovShiftedLayerImage_upperBound R f n hn 1

lemma postnikovImageCoefficient_lowerBound :
    (bimoduleRestrict (postnikovImageBase R f n hn)
      (postnikovShiftedLayerImage R f n hn 1)).X.IsStrictlyGE (-(n + 1) - 1) :=
  postnikovShiftedLayerImage_lowerBound R f n hn 1

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
