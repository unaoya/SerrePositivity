module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoFixedRightDirectSourceModel

/-!
概要：source 模型経路の始点を、元の source 比較と直接 B 遷移の実模型合成へ同定する。
方針：元の左脚・右脚・全経路を係数復元三角形で同時に比較する。
規約：元の実模型合成を始点に保持。使われ方：直接遷移と fixed 候補の右三角形。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} {f : LevelHom A B}
  {j : ℕ} (d : PostnikovTwoClassInverseData R f j)

def directOriginalModelMap := d.sourceRelativeComparison R ≫ d.sourceToOriginalModel R ≫
  postnikovClassModelMap R 1 (by omega)
    (postnikovCommonRightDenDirectMap R f d.baseInverse d.layerInverse d.target_le)

lemma directSourceInitialModelMap_eq_original : d.directSourceInitialModelMap R =
    d.directOriginalModelMap R := by
  let M := d.denominatorLayer R
  let a := d.sourceClass R
  let cL := SquareZeroExtension.relativeComparison_left M a
  let cR := SquareZeroExtension.relativeComparison_right M a
  let cP := SquareZeroExtension.relativeComparison_path M a
  apply HomotopyPullbackModel.hom_ext R (postnikovPerturbedClass R (B.obj j).obj 1 (by omega))
    (SquareZero.zeroSection (postnikov R (B.obj j).obj 1)
      (directNativeLayer (B := B) (j := j) R))
  · rw [d.directSourceInitialModelMap_left R]
    simp only [directOriginalModelMap, sourceRelativeComparison, Category.assoc,
      postnikovClassModelMap_left, reassoc_of% (d.sourceToOriginalModel_left R)]
    rw [reassoc_of% cL]
    simp only [directNativeSource, Category.assoc]
    rfl
  · rw [d.directSourceInitialModelMap_right R]
    simp only [directOriginalModelMap, sourceRelativeComparison, Category.assoc,
      postnikovClassModelMap_right, reassoc_of% (d.sourceToOriginalModel_right R)]
    rw [reassoc_of% cR]
    rfl
  · rw [d.directSourceInitialModelMap_path R, d.directInitialNativeWitness_hom R]
    simp only [directOriginalModelMap, sourceRelativeComparison, Category.assoc,
      postnikovClassModelMap_path, reassoc_of% (d.sourceToOriginalModel_path R)]
    rw [reassoc_of% cP]
    let h := congrArg (fun t => SquareZeroExtension.relativePath M a ≫ Path.map R t)
      (d.rightDenominatorCoefficient_restore R)
    let k := congrArg (fun t => SquareZeroExtension.relativePath M a ≫ t)
      (Path.map_comp R (SquareZero.baseChangeMap (d.lowerBaseInverse R).roof.denominator
        (postnikovShiftedLayerBimodule R (B.obj d.layerInverse.zero.stage).obj 1 (by omega) 1))
        (postnikovDerivationTargetMap R
          (postnikovCommonRightDenDirectMap R f d.baseInverse d.layerInverse d.target_le)
          1 (by omega)))
    exact h.trans k

def directOriginalSourceModelHomotopy : Path.Witness R (d.directOriginalModelMap R)
    (d.directSourceFinalModelMap R) where
  hom := (d.directSourceModelHomotopy R).hom
  source_eq := (d.directSourceModelHomotopy R).source_eq.trans
    (d.directSourceInitialModelMap_eq_original R)
  target_eq := (d.directSourceModelHomotopy R).target_eq

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
