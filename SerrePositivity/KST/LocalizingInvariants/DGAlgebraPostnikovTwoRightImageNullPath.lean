module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoRightImageSourcePath
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroSourceModelHomotopy

/-!
概要：元の右像の相対模型が持つ零経路を、Bⱼ の native class 標的へ戻す。
方針：元の relativePath を係数復元で移し、両脚と底の定数経路を保持する。
規約：零経路の存在を追加仮定にしない。使われ方：source 自然性と W の実模型比較。
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

lemma rightImageClass_projection : d.rightImageClass R ≫ SquareZero.projection _ _ =
    d.classProjection R := by
  rw [rightImageClass, Category.assoc, SquareZero.coefficientMap_projection]
  exact (d.classRelativeWitness R).target_projection

lemma rightImageRelativeRight :
    SquareZeroExtension.relativeRight (d.rightClassifyingLayer R) (d.rightImageClass R) =
    SquareZeroExtension.relativeLeft (d.rightClassifyingLayer R) (d.rightImageClass R) ≫
      d.classProjection R := by
  rw [SquareZeroExtension.relativeRight_eq, d.rightImageClass_projection R]

def rightImageNativeNullPath : SquareZero.RelativeWitness
    (SquareZeroExtension.relativeRight (d.rightClassifyingLayer R) (d.rightImageClass R) ≫
      postnikovCommonClassRightImageBase R f d.baseInverse d.layerInverse d.target_le)
    (postnikovShiftedLayerBimodule R (B.obj j).obj 1 (by omega) 1)
    ((SquareZeroExtension.relativeLeft (d.rightClassifyingLayer R) (d.rightImageClass R) ≫
      d.rightImageNativeSource R) ≫ postnikovPerturbedClass R (B.obj j).obj 1 (by omega))
    ((SquareZeroExtension.relativeRight (d.rightClassifyingLayer R) (d.rightImageClass R) ≫
      postnikovCommonClassRightImageBase R f d.baseInverse d.layerInverse d.target_le) ≫
        SquareZero.zeroSection (postnikov R (B.obj j).obj 1)
          (postnikovShiftedLayerBimodule R (B.obj j).obj 1 (by omega) 1)) where
  hom := SquareZeroExtension.relativePath (d.rightClassifyingLayer R) (d.rightImageClass R) ≫
    Path.map R (d.rightImageClassRestore R)
  source_eq := by
    have h := ((SquareZeroExtension.relativeWitness (d.rightClassifyingLayer R)
      (d.rightImageClass R)).toWitness.postcomp (d.rightImageClassRestore R)).source_eq
    exact h.trans ((Category.assoc _ _ _).trans
      ((congrArg (fun t => SquareZeroExtension.relativeLeft (d.rightClassifyingLayer R)
        (d.rightImageClass R) ≫ t) (d.rightImageClass_restore R)).trans
          (Category.assoc _ _ _).symm))
  target_eq := by
    have h := ((SquareZeroExtension.relativeWitness (d.rightClassifyingLayer R)
      (d.rightImageClass R)).toWitness.postcomp (d.rightImageClassRestore R)).target_eq
    exact h.trans ((Category.assoc _ _ _).trans
      ((congrArg (fun t => SquareZeroExtension.relativeRight (d.rightClassifyingLayer R)
        (d.rightImageClass R) ≫ t) (SquareZero.coefficientRestore_zeroSection _ _ _)).trans
          (Category.assoc _ _ _).symm))
  projection_eq := by
    change (_ ≫ Path.map R (SquareZero.coefficientRestore
      (postnikovCommonClassRightImageBase R f d.baseInverse d.layerInverse d.target_le)
      (postnikovShiftedLayerBimodule R (B.obj j).obj 1 (by omega) 1)
      (d.rightImageCoefficientIso R))) ≫ _ = _
    rw [Category.assoc, ← Path.map_comp, SquareZero.coefficientRestore_projection,
      Path.map_comp, ← Category.assoc, SquareZeroExtension.relativePath_base]
    simp only [Category.assoc, Path.diagonal_naturality]
    rw [← reassoc_of% (SquareZeroExtension.relativeRight_eq
      (d.rightClassifyingLayer R) (d.rightImageClass R))]

def rightImageModelSourcePath : Path.Witness R
    (SquareZeroExtension.relativeLeft (d.rightClassifyingLayer R) (d.rightImageClass R) ≫
      d.rightImageNativeSource R)
    (SquareZeroExtension.relativeLeft (d.rightClassifyingLayer R) (d.rightImageClass R) ≫
      ((postnikovCommonRightGammaSourceWitness R f d.baseInverse d.layerInverse d.target_le).hom ≫
        Path.source R (postnikovPerturbedExtension R (B.obj j).obj 1 (by omega)))) where
  hom := SquareZeroExtension.relativeLeft (d.rightClassifyingLayer R) (d.rightImageClass R) ≫
    (d.rightImageSourcePath R).hom
  source_eq := by rw [Category.assoc, d.rightImageSourcePath_source R]
  target_eq := by rw [Category.assoc, d.rightImageSourcePath_target R]

lemma rightImageModelSourcePath_relative :
    ((d.rightImageModelSourcePath R).postcomp
      (postnikovPerturbedClass R (B.obj j).obj 1 (by omega))).hom ≫
        Path.map R (SquareZero.projection _ _) =
    (SquareZeroExtension.relativeRight (d.rightClassifyingLayer R) (d.rightImageClass R) ≫
      postnikovCommonClassRightImageBase R f d.baseInverse d.layerInverse d.target_le) ≫
        Path.diagonal R (postnikov R (B.obj j).obj 1) := by
  change ((_ ≫ (d.rightImageSourcePath R).hom) ≫ _) ≫ _ = _
  rw [Category.assoc, ← Path.map_comp, postnikovPerturbedClass_projection,
    Category.assoc, d.rightImageSourcePath_relative R]
  simp only [← Category.assoc]
  rw [← d.rightImageRelativeRight R]

def rightImageSourceModelHomotopy := SquareZeroExtension.sourceModelHomotopy
  (postnikovShiftedLayerBimodule R (B.obj j).obj 1 (by omega) 1)
  (postnikovPerturbedClass R (B.obj j).obj 1 (by omega))
  (SquareZeroExtension.relativeRight (d.rightClassifyingLayer R) (d.rightImageClass R) ≫
    postnikovCommonClassRightImageBase R f d.baseInverse d.layerInverse d.target_le)
  (d.rightImageModelSourcePath R) (d.rightImageModelSourcePath_relative R)
  (d.rightImageNativeNullPath R)

lemma rightImageOriginalModel_as_lift :
    SquareZeroExtension.sourceModelInitialMap
      (postnikovShiftedLayerBimodule R (B.obj j).obj 1 (by omega) 1)
      (postnikovPerturbedClass R (B.obj j).obj 1 (by omega))
      (SquareZeroExtension.relativeRight (d.rightClassifyingLayer R) (d.rightImageClass R) ≫
        postnikovCommonClassRightImageBase R f d.baseInverse d.layerInverse d.target_le)
      (d.rightImageNativeNullPath R) = d.rightImageRelativeToOriginalModel R := by
  apply HomotopyPullbackModel.hom_ext R
    (postnikovPerturbedClass R (B.obj j).obj 1 (by omega))
    (SquareZero.zeroSection (postnikov R (B.obj j).obj 1)
      (postnikovShiftedLayerBimodule R (B.obj j).obj 1 (by omega) 1))
  · change HomotopyPullbackModel.lift R _ _ _ _ _ ≫ _ = _
    rw [HomotopyPullbackModel.lift_left, rightImageRelativeToOriginalModel, Category.assoc,
      d.rightImageToOriginalModel_left R, ← Category.assoc,
      SquareZeroExtension.relativeComparison_left]
  · change HomotopyPullbackModel.lift R _ _ _ _ _ ≫ _ = _
    rw [HomotopyPullbackModel.lift_right, rightImageRelativeToOriginalModel, Category.assoc,
      d.rightImageToOriginalModel_right R, ← Category.assoc,
      SquareZeroExtension.relativeComparison_right]
  · change HomotopyPullbackModel.lift R _ _ _ _ _ ≫ _ = _
    rw [HomotopyPullbackModel.lift_path]
    conv_rhs =>
      rw [rightImageRelativeToOriginalModel, Category.assoc,
        d.rightImageToOriginalModel_path R, ← Category.assoc,
        SquareZeroExtension.relativeComparison_path]
    rfl

def rightImageToGammaModel := SquareZeroExtension.sourceModelFinalMap
  (postnikovShiftedLayerBimodule R (B.obj j).obj 1 (by omega) 1)
  (postnikovPerturbedClass R (B.obj j).obj 1 (by omega))
  (SquareZeroExtension.relativeRight (d.rightClassifyingLayer R) (d.rightImageClass R) ≫
    postnikovCommonClassRightImageBase R f d.baseInverse d.layerInverse d.target_le)
  (d.rightImageModelSourcePath R) (d.rightImageModelSourcePath_relative R)
  (d.rightImageNativeNullPath R)

def rightImageOriginalSourceModelHomotopy : Path.Witness R
    (d.rightImageRelativeToOriginalModel R) (d.rightImageToGammaModel R) where
  hom := (d.rightImageSourceModelHomotopy R).hom
  source_eq := (d.rightImageSourceModelHomotopy R).source_eq.trans
    (d.rightImageOriginalModel_as_lift R)
  target_eq := (d.rightImageSourceModelHomotopy R).target_eq

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
