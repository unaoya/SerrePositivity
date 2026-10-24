module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonClassFixedRightNaturality

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreClassFixedRightComposite
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreSpecialization

/-!
概要：元の fixed class 互換性と fⱼ の自然性の合成を、G⁻¹⋅標準自然性へ全射で同定する。
方針：元の互換性の反転合成式と、移送後の affine 結合則を使う。
規約：元の native 互換性・自然性の全射を保持。使われ方：元の W を接ぐ右三角形。
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

def postnikovCommonClassGlueStandardPath :=
  PostnikovCommonCore.postnikovCommonClassGlueStandardPath
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

variable (e : PostnikovZeroLayerInverse R 1 f j i hj)

lemma postnikovCommonClassFixedCompatibilityNaturality_hom :
    (postnikovCommonClassFixedCompatibilityNaturality R f c d hj e).hom =
      (postnikovCommonClassGlueStandardPath R f c d hj).hom :=
  PostnikovCommonCore.postnikovCommonClassFixedCompatibilityNaturality_hom
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj) (e := e)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
