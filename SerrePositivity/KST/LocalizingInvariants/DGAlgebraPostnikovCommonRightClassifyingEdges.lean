module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovClassZeroNaturality
public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightClassifyingBaseContour
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightAffineFixedGlue

/-!
概要：P 上の classifying 正方形の元の中央辺と、既存の三経路貼合せの中央辺を同定する。
方針：零底射の自然性と全二重 class 射影を使う。
規約：元の指定経路全体の厳密等式。使われ方：affine 貼合せの右合成比較。
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

lemma postnikovCommonRightClassifyingBase_zero : postnikovCommonRightClassifyingBase R f c d hj =
    postnikovCommonRightZeroBase R f c d ≫ postnikovMap R (B.transition hj).hom 0 := by
  rw [postnikovCommonRightClassifyingBase, postnikovTransition_naturality,
    ← Category.assoc, ← postnikovCommonRightZeroBase_num]

lemma postnikovCommonRightClassifyingZeroSquare_source_fixed :
    (postnikovCommonRightClassifyingZeroSquare R f c d hj).hom ≫
      Path.source R (Path.algebra R (postnikovZeroClassTarget R (B.obj j).obj 1 1)) =
    cellAugmentation R (postnikovCommonRightCellSource R f c d) ≫
      (postnikovCommonRightFixedCentralRelative R f c d).hom ≫
        Path.map R (postnikovZeroClassMap R 1 1 (B.transition hj).hom) := by
  rw [(postnikovCommonRightClassifyingZeroSquare R f c d hj).source_eq]
  change ((cellAugmentation R (postnikovCommonRightCellSource R f c d) ≫
    (postnikovCommonRightFixedCellClassWitness R f c d).hom ≫
      Path.map R (postnikovDerivationTargetMap R (B.transition hj).hom 1 (by omega))) ≫
        Path.map R (postnikovClassToZeroBase R (B.obj j).obj 1 (by omega) 1)) =
    cellAugmentation R (postnikovCommonRightCellSource R f c d) ≫
      ((postnikovCommonRightFixedCellClassWitness R f c d).hom ≫
        Path.map R (postnikovClassToZeroBase R (B.obj i).obj 1 (by omega) 1)) ≫
          Path.map R (postnikovZeroClassMap R 1 1 (B.transition hj).hom)
  simp only [Category.assoc, ← Path.map_comp, postnikovClassToZeroBase_naturality]

lemma postnikovCommonRightClassifyingBaseChangeHom_source_fixed :
    (postnikovCommonRightClassifyingBaseChangeHom R f c d hj ≫
      Path.source R (Path.algebra R (SquareZero.algebra (postnikovCommonClassBase R f c d)
        (bimoduleRestrict (postnikovCommonRightClassifyingBase R f c d hj)
          (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1))))) ≫
      Path.map R (SquareZero.baseChangeMap (postnikovCommonRightClassifyingBase R f c d hj)
        (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1)) =
    cellAugmentation R (postnikovCommonRightCellSource R f c d) ≫
      (postnikovCommonRightFixedCentralRelative R f c d).hom ≫
        Path.map R (postnikovZeroClassMap R 1 1 (B.transition hj).hom) := by
  rw [Category.assoc, ← Path.map_source, ← Category.assoc,
    postnikovCommonRightClassifyingBaseChangeHom_map]
  exact postnikovCommonRightClassifyingZeroSquare_source_fixed R f c d hj

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
