module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonClassFixedZeroPaths
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeReverseCongr

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreClassFixedZeroComposition
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreSpecialization

/-!
概要：fixed Γ の右 class 像を反転と標準像の実 affine 合成として同定する。
方針：前合成・底付き移送による反転合成の保存を元の二経路へ適用する。
規約：線形式だけでなく全乗法的経路を比較。使われ方：元の自然性二重経路への接続。
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
  (e : PostnikovZeroLayerInverse R 1 f j i hj)

lemma postnikovCommonClassFixedCompatibilityMapped_hom :
    (postnikovCommonClassFixedCompatibilityMappedRelative R f c d hj e).hom =
      ((postnikovCommonClassFixedTransitionMappedRelative R f c d hj e).reverse.comp
        (postnikovCommonClassFixedStandardMappedRelative R f c d hj)).hom :=
  PostnikovCommonCore.postnikovCommonClassFixedCompatibilityMapped_hom
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj) (e := e)

lemma postnikovCommonClassFixedTransitionMapped_glue :
    (postnikovCommonClassFixedTransitionMappedRelative R f c d hj e).hom =
      (postnikovCommonRightGlueZeroRelative R f c d hj).hom :=
  PostnikovCommonCore.postnikovCommonClassFixedTransitionMapped_glue
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj) (e := e)

lemma postnikovCommonClassFixedTransitionMapped_reverse_glue :
    (postnikovCommonClassFixedTransitionMappedRelative R f c d hj e).reverse.hom =
      (postnikovCommonRightGlueZeroRelative R f c d hj).reverse.hom :=
  PostnikovCommonCore.postnikovCommonClassFixedTransitionMapped_reverse_glue
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj) (e := e)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
