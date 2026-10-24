module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightGammaSource
public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightContourBottomPath
public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovNativeZeroCoefficientIso

/-!
概要：Γ 上の W source の全 class 経路を、既存の零底の輪郭経路へ同定する。
方針：二重経路の底変更と終点評価を可換させ、元の W の全射を回収する。
規約：class の端点だけによる同定を使わない。使われ方：native 模型比較の hk 入力。
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

lemma postnikovCommonRightToClassifying_source :
    postnikovCommonRightToClassifying R hn f c d ≫
      cellAugmentation R (postnikovCommonRightCellSource R hn f c d) =
        postnikovCommonRightGammaToSource R hn f c d := by
  rw [postnikovCommonRightToClassifying, Category.assoc,
    cellPathNonpositiveToCell_projection]
  rfl

lemma postnikovCommonRightContourBottomPath_map :
    (postnikovCommonRightContourBottomPath R hn f c d hj).hom ≫
      Path.map R (SquareZero.baseChangeMap
        (postnikovCommonRightClassifyingBase R hn f c d hj)
        (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj n) 1)) =
    (cellAugmentation R (postnikovCommonRightCellSource R hn f c d) ≫
      (postnikovCommonRightFixedMappedClassWitness R hn f c d hj).hom) ≫
        Path.map R (postnikovClassToZeroBase R (B.obj j).obj n hn 1) := by
  change (_ ≫ Path.target R _) ≫ Path.map R _ = _
  rw [Category.assoc, ← Path.map_target, ← Category.assoc,
    postnikovCommonRightClassifyingBaseChangeHom_map]
  exact (postnikovCommonRightClassifyingZeroSquare R hn f c d hj).target_eq

lemma postnikovCommonRightGammaSourceWitness_zeroClass :
    ((postnikovCommonRightGammaSourceWitness R hn f c d hj).hom ≫
      Path.map R (postnikovPerturbedClass R (B.obj j).obj n hn)) ≫
        Path.map R (postnikovClassToZeroBase R (B.obj j).obj n hn 1) =
    (postnikovCommonRightContourBottomRefinedPath R hn f c d hj).hom ≫
      Path.map R (SquareZero.baseChangeMap
        (postnikovCommonRightClassifyingBase R hn f c d hj)
        (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj n) 1)) := by
  rw [postnikovCommonRightGammaSourceWitness_class]
  change (_ ≫ _) ≫ _ =
    (postnikovCommonRightToClassifying R hn f c d ≫
      (postnikovCommonRightContourBottomPath R hn f c d hj).hom) ≫ _
  have h := congrArg (fun t => postnikovCommonRightToClassifying R hn f c d ≫ t)
    (postnikovCommonRightContourBottomPath_map R hn f c d hj)
  simpa only [← Category.assoc, postnikovCommonRightToClassifying_source] using h.symm

lemma postnikovCommonRightGammaSourceWitness_nativeClass :
    ((postnikovCommonRightGammaSourceWitness R hn f c d hj).hom ≫
      Path.map R (postnikovPerturbedClass R (B.obj j).obj n hn)) ≫
        Path.map R ((postnikovNativeZeroIso R (B.obj j).obj n hn 1).hom ≫
          SquareZero.baseChangeMap (postnikovTransition R (B.obj j).obj n 0 (by omega))
            (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj n) 1)) =
    (postnikovCommonRightContourBottomRefinedPath R hn f c d hj).hom ≫
      Path.map R (SquareZero.baseChangeMap
        (postnikovCommonRightClassifyingBase R hn f c d hj)
        (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj n) 1)) := by
  rw [postnikovNativeZeroIso_map]
  exact postnikovCommonRightGammaSourceWitness_zeroClass R hn f c d hj

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
