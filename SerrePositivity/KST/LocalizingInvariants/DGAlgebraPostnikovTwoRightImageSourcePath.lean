module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoRightGammaEndpoints

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSuccessorRightImageSourcePath

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
      postnikovCommonRightBase R f c d ≫ postnikovMap R (B.transition hj).hom 1 :=
  PostnikovCommonCore.postnikovCommonClassRightImageBase_composite
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra

namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} {f : LevelHom A B}
  {j : ℕ} (d : PostnikovTwoClassInverseData R f j)

def rightImageSourcePath :=
  PostnikovSuccessorClassInverseData.rightImageSourcePath
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma rightImageSourcePath_source : (d.rightImageSourcePath R).hom ≫
    Path.source R (postnikovPerturbedExtension R (B.obj j).obj 1 (by omega)) =
      d.rightImageNativeSource R :=
  PostnikovSuccessorClassInverseData.rightImageSourcePath_source
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma rightImageSourcePath_target : (d.rightImageSourcePath R).hom ≫
    Path.target R (postnikovPerturbedExtension R (B.obj j).obj 1 (by omega)) =
    (postnikovCommonRightGammaSourceWitness R f d.baseInverse d.layerInverse d.target_le).hom ≫
      Path.source R (postnikovPerturbedExtension R (B.obj j).obj 1 (by omega)) :=
  PostnikovSuccessorClassInverseData.rightImageSourcePath_target
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma rightImageSourcePath_relative : (d.rightImageSourcePath R).hom ≫
    Path.map R (postnikovPerturbedProjection R (B.obj j).obj 1 (by omega)) =
    (d.classProjection R ≫ postnikovCommonClassRightImageBase R f d.baseInverse
      d.layerInverse d.target_le) ≫ Path.diagonal R (postnikov R (B.obj j).obj 1) :=
  PostnikovSuccessorClassInverseData.rightImageSourcePath_relative
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma rightImageSourcePath_class : (d.rightImageSourcePath R).hom ≫
    Path.map R (postnikovPerturbedClass R (B.obj j).obj 1 (by omega)) =
    postnikovCommonRightImageToSecond R f d.baseInverse d.layerInverse ≫
      (postnikovCellClassOverNaturalityWitness R (A.obj j).obj (B.obj j).obj
        (d.classBase R) 1 (by omega) (d.targetBase R) (f.app j).hom).hom :=
  PostnikovSuccessorClassInverseData.rightImageSourcePath_class
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma rightImageSourcePath_zeroClass :
    ((d.rightImageSourcePath R).hom ≫
      Path.map R (postnikovPerturbedClass R (B.obj j).obj 1 (by omega))) ≫
        Path.map R (postnikovClassToZeroBase R (B.obj j).obj 1 (by omega) 1) =
    (postnikovCommonClassFixedRightNaturality R f d.baseInverse d.layerInverse
      d.target_le).hom :=
  PostnikovSuccessorClassInverseData.rightImageSourcePath_zeroClass
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
