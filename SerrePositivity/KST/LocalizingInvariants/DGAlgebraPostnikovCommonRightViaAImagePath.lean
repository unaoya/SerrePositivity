module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightViaBImagePath
public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightZeroAffineRefinement

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightViaAImagePath
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreSpecialization

/-!
概要：元の Γ 源上の A 遷移≫fⱼの零底 affine 経路を、元の二 ImageWitness の合成で表示する。
方針：因子分解経路の実同定を前合成し、係数同型の逆と元の零底同型で後合成する。
規約：新しい経路を選ばない。使われ方：native 標準経路と fⱼ の自然性 の境界経路との照合。
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

def postnikovCommonRightViaAImageComposite :=
  PostnikovCommonCore.postnikovCommonRightViaAImageComposite
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

def postnikovCommonRightViaAImageIso :=
  PostnikovCommonCore.postnikovCommonRightViaAImageIso
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

def postnikovCommonRightViaAImageToZero :=
  PostnikovCommonCore.postnikovCommonRightViaAImageToZero
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

/-- 元の零底 Γ 経路は、指定した二自然性経路の affine 合成の同じ像に厳密に一致。 -/
lemma postnikovCommonRightZeroAffineViaA_image_hom :
    (postnikovCommonRightZeroAffineViaA R f c d hj).hom =
    postnikovCommonRightImageToSecond R f c d ≫
      (postnikovCommonRightViaAImageComposite R f c d hj).hom ≫
        Path.map R (postnikovCommonRightViaAImageToZero R f c d hj) :=
  PostnikovCommonCore.postnikovCommonRightZeroAffineViaA_image_hom
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
