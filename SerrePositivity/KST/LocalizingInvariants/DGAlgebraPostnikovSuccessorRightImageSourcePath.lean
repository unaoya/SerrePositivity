module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSuccessorRightGammaEndpoints

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
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
open ProExcision
variable (R : Type u) [CommRing R] {n : ℤ} (hn : 0 ≤ n) {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (postnikovFunctor R n)) i m hi)
  (d : PostnikovCommonCore.LayerInverse R hn f c) {j : ℕ} (hj : j ≤ i)

lemma postnikovCommonClassRightImageBase_composite :
    PostnikovCommonCore.postnikovCommonClassRightImageBase R hn f c d hj =
      PostnikovCommonCore.postnikovCommonRightBase R hn f c d ≫ postnikovMap R (B.transition hj).hom n := by
  change ((PostnikovCommonCore.roofRefine R hn f c d.zero.source_le).roof.numerator ≫
    (postnikovFunctor R n).map (A.transition hj)) ≫ (postnikovFunctor R n).map (f.app j) =
    ((PostnikovCommonCore.roofRefine R hn f c d.zero.source_le).roof.numerator ≫
      (postnikovFunctor R n).map (f.app i)) ≫ (postnikovFunctor R n).map (B.transition hj)
  simp only [Category.assoc]
  exact congrArg (fun t => (PostnikovCommonCore.roofRefine R hn f c d.zero.source_le).roof.numerator ≫ t)
    ((f.map (postnikovFunctor R n)).naturality hj)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore

namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovSuccessorClassInverseData
open ProExcision
variable (R : Type u) [CommRing R] {n : ℤ} {hn : 0 ≤ n} {A B : Tower (NonpositiveAlgebra R)} {f : LevelHom A B}
  {j : ℕ} (d : PostnikovSuccessorClassInverseData R hn f j)

def rightImageSourcePath :=
  (postnikovCellLiftOverNaturalityWitness R (A.obj j).obj (B.obj j).obj
    (d.classBase R) n hn (d.targetBase R) (f.app j).hom).precomp
      (PostnikovCommonCore.postnikovCommonRightImageToSecond R hn f d.baseInverse d.layerInverse)

lemma rightImageSourcePath_source : (d.rightImageSourcePath R).hom ≫
    Path.source R (postnikovPerturbedExtension R (B.obj j).obj n hn) =
      d.rightImageNativeSource R := by
  rw [(d.rightImageSourcePath R).source_eq]
  simp only [postnikovCellLiftOverSource, rightImageNativeSource, targetCellMap, Category.assoc]
  rw [reassoc_of% (PostnikovCommonCore.postnikovCommonRightImageToSecond_toCell R hn f d.baseInverse d.layerInverse)]

lemma rightImageSourcePath_target : (d.rightImageSourcePath R).hom ≫
    Path.target R (postnikovPerturbedExtension R (B.obj j).obj n hn) =
    (PostnikovCommonCore.postnikovCommonRightGammaSourceWitness R hn f d.baseInverse d.layerInverse d.target_le).hom ≫
      Path.source R (postnikovPerturbedExtension R (B.obj j).obj n hn) := by
  rw [(d.rightImageSourcePath R).target_eq, PostnikovCommonCore.postnikovCommonRightGammaSourceWitness_source]
  simp only [postnikovCellLiftOverTarget, Category.assoc]
  rw [reassoc_of% (PostnikovCommonCore.postnikovCommonRightImageToSecond_toCell R hn f d.baseInverse d.layerInverse)]
  change _ = PostnikovCommonCore.postnikovCommonClassCompatibilityToCell R hn f d.baseInverse d.layerInverse ≫
    cellResolutionMap R (PostnikovCommonCore.postnikovCommonRightBase R hn f d.baseInverse d.layerInverse ≫
      postnikovMap R (B.transition d.target_le).hom n) ≫ _
  rw [← PostnikovCommonCore.postnikovCommonClassRightImageBase_composite]
  rfl

lemma rightImageSourcePath_relative : (d.rightImageSourcePath R).hom ≫
    Path.map R (postnikovPerturbedProjection R (B.obj j).obj n hn) =
    (d.classProjection R ≫ PostnikovCommonCore.postnikovCommonClassRightImageBase R hn f d.baseInverse
      d.layerInverse d.target_le) ≫ Path.diagonal R (postnikov R (B.obj j).obj n) := by
  change (PostnikovCommonCore.postnikovCommonRightImageToSecond R hn f d.baseInverse d.layerInverse ≫ _) ≫ _ = _
  rw [Category.assoc, postnikovCellLiftOverNaturalityWitness_relative]
  simp only [Category.assoc]
  rw [reassoc_of% (PostnikovCommonCore.postnikovCommonRightImageToSecond_projection R hn f d.baseInverse d.layerInverse)]
  rfl

lemma rightImageSourcePath_class : (d.rightImageSourcePath R).hom ≫
    Path.map R (postnikovPerturbedClass R (B.obj j).obj n hn) =
    PostnikovCommonCore.postnikovCommonRightImageToSecond R hn f d.baseInverse d.layerInverse ≫
      (postnikovCellClassOverNaturalityWitness R (A.obj j).obj (B.obj j).obj
        (d.classBase R) n hn (d.targetBase R) (f.app j).hom).hom := by
  change (PostnikovCommonCore.postnikovCommonRightImageToSecond R hn f d.baseInverse d.layerInverse ≫ _) ≫ _ = _
  rw [Category.assoc]
  rfl

lemma rightImageSourcePath_zeroClass :
    ((d.rightImageSourcePath R).hom ≫
      Path.map R (postnikovPerturbedClass R (B.obj j).obj n hn)) ≫
        Path.map R (postnikovClassToZeroBase R (B.obj j).obj n hn 1) =
    (PostnikovCommonCore.postnikovCommonClassFixedRightNaturality R hn f d.baseInverse d.layerInverse
      d.target_le).hom := by
  rw [d.rightImageSourcePath_class R]
  change (_ ≫ _) ≫ _ =
    (PostnikovCommonCore.postnikovCommonRightViaASecondZeroPath R hn f d.baseInverse d.layerInverse d.target_le).hom ≫
      Path.map R (SquareZero.baseChangeMap
        (PostnikovCommonCore.postnikovCommonRightClassifyingBase R hn f d.baseInverse d.layerInverse d.target_le)
        (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj n) 1))
  exact (Category.assoc _ _ _).trans
    (PostnikovCommonCore.postnikovCommonRightViaASecondZeroPath_map R hn f d.baseInverse d.layerInverse d.target_le).symm

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovSuccessorClassInverseData
