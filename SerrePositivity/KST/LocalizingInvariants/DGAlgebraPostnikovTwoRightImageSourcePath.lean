module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoRightGammaEndpoints

/-!
概要：元の fⱼ の像から Γ 上の W source の始点までを、一定底の実 source 経路で結ぶ。
方針：fⱼ の cell lift 自然性を元の Γ に前合成し、塔の自然性で始点を照合する。
規約：元の fⱼ 自然性の全 class 経路を保持。使われ方：W 適用前の模型比較。
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

lemma postnikovCommonClassRightImageBase_composite :
    postnikovCommonClassRightImageBase R f c d hj =
      postnikovCommonRightBase R f c d ≫ postnikovMap R (B.transition hj).hom 1 := by
  change ((postnikovOneRoofRefine R f c d.zero.source_le).roof.numerator ≫
    (postnikovFunctor R 1).map (A.transition hj)) ≫ (postnikovFunctor R 1).map (f.app j) =
    ((postnikovOneRoofRefine R f c d.zero.source_le).roof.numerator ≫
      (postnikovFunctor R 1).map (f.app i)) ≫ (postnikovFunctor R 1).map (B.transition hj)
  simp only [Category.assoc]
  exact congrArg (fun t => (postnikovOneRoofRefine R f c d.zero.source_le).roof.numerator ≫ t)
    ((f.map (postnikovFunctor R 1)).naturality hj)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra

namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} {f : LevelHom A B}
  {j : ℕ} (d : PostnikovTwoClassInverseData R f j)

def rightImageSourcePath :=
  (postnikovCellLiftOverNaturalityWitness R (A.obj j).obj (B.obj j).obj
    (d.classBase R) 1 (by omega) (d.targetBase R) (f.app j).hom).precomp
      (postnikovCommonRightImageToSecond R f d.baseInverse d.layerInverse)

lemma rightImageSourcePath_source : (d.rightImageSourcePath R).hom ≫
    Path.source R (postnikovPerturbedExtension R (B.obj j).obj 1 (by omega)) =
      d.rightImageNativeSource R := by
  rw [(d.rightImageSourcePath R).source_eq]
  simp only [postnikovCellLiftOverSource, rightImageNativeSource, targetCellMap, Category.assoc]
  rw [reassoc_of% (postnikovCommonRightImageToSecond_toCell R f d.baseInverse d.layerInverse)]

lemma rightImageSourcePath_target : (d.rightImageSourcePath R).hom ≫
    Path.target R (postnikovPerturbedExtension R (B.obj j).obj 1 (by omega)) =
    (postnikovCommonRightGammaSourceWitness R f d.baseInverse d.layerInverse d.target_le).hom ≫
      Path.source R (postnikovPerturbedExtension R (B.obj j).obj 1 (by omega)) := by
  rw [(d.rightImageSourcePath R).target_eq, postnikovCommonRightGammaSourceWitness_source]
  simp only [postnikovCellLiftOverTarget, Category.assoc]
  rw [reassoc_of% (postnikovCommonRightImageToSecond_toCell R f d.baseInverse d.layerInverse)]
  change _ = postnikovCommonClassCompatibilityToCell R f d.baseInverse d.layerInverse ≫
    cellResolutionMap R (postnikovCommonRightBase R f d.baseInverse d.layerInverse ≫
      postnikovMap R (B.transition d.target_le).hom 1) ≫ _
  rw [← postnikovCommonClassRightImageBase_composite]
  rfl

lemma rightImageSourcePath_relative : (d.rightImageSourcePath R).hom ≫
    Path.map R (postnikovPerturbedProjection R (B.obj j).obj 1 (by omega)) =
    (d.classProjection R ≫ postnikovCommonClassRightImageBase R f d.baseInverse
      d.layerInverse d.target_le) ≫ Path.diagonal R (postnikov R (B.obj j).obj 1) := by
  change (postnikovCommonRightImageToSecond R f d.baseInverse d.layerInverse ≫ _) ≫ _ = _
  rw [Category.assoc, postnikovCellLiftOverNaturalityWitness_relative]
  simp only [Category.assoc]
  rw [reassoc_of% (postnikovCommonRightImageToSecond_projection R f d.baseInverse d.layerInverse)]
  rfl

lemma rightImageSourcePath_class : (d.rightImageSourcePath R).hom ≫
    Path.map R (postnikovPerturbedClass R (B.obj j).obj 1 (by omega)) =
    postnikovCommonRightImageToSecond R f d.baseInverse d.layerInverse ≫
      (postnikovCellClassOverNaturalityWitness R (A.obj j).obj (B.obj j).obj
        (d.classBase R) 1 (by omega) (d.targetBase R) (f.app j).hom).hom := by
  change (postnikovCommonRightImageToSecond R f d.baseInverse d.layerInverse ≫ _) ≫ _ = _
  rw [Category.assoc]
  rfl

lemma rightImageSourcePath_zeroClass :
    ((d.rightImageSourcePath R).hom ≫
      Path.map R (postnikovPerturbedClass R (B.obj j).obj 1 (by omega))) ≫
        Path.map R (postnikovClassToZeroBase R (B.obj j).obj 1 (by omega) 1) =
    (postnikovCommonClassFixedRightNaturality R f d.baseInverse d.layerInverse
      d.target_le).hom := by
  rw [d.rightImageSourcePath_class R]
  change (_ ≫ _) ≫ _ =
    (postnikovCommonRightViaASecondZeroPath R f d.baseInverse d.layerInverse d.target_le).hom ≫
      Path.map R (SquareZero.baseChangeMap
        (postnikovCommonRightClassifyingBase R f d.baseInverse d.layerInverse d.target_le)
        (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1))
  exact (Category.assoc _ _ _).trans
    (postnikovCommonRightViaASecondZeroPath_map R f d.baseInverse d.layerInverse d.target_le).symm

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
