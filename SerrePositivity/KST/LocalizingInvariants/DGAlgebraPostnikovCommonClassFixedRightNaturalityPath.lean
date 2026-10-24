module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonClassFixedZeroComposition
public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonClassGlueStandardBottom
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeFollowingTransfer

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreClassFixedRightNaturalityPath
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreSpecialization

/-!
概要：元の native 標準経路に fⱼ の自然性を接合し、fixed class 互換性にも接合する。
方針：標準経路の全射同定から、後続自然性の接合端点と底を移す。
規約：native 経路の端点と全射を保持。使われ方：fixed class 自身の右三角形比較。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (postnikovFunctor R 1)) i m hi)
  (d : PostnikovCommonLayerInverse R f c) {j : ℕ} (hj : j ≤ i)

def postnikovCommonClassFixedNaturalityEndpoint :
    postnikovCommonClassStandardGlueSource R f c d ⟶
      postnikovZeroClassTarget R (B.obj j).obj 1 1 :=
  PostnikovCommonCore.postnikovCommonClassFixedNaturalityEndpoint
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

lemma postnikovCommonClassFixedStandard_reference_hom :
    (postnikovCommonClassStandardContourRelative R f c d hj).hom =
      (postnikovCommonClassFixedStandardMappedRelative R f c d hj).hom :=
  PostnikovCommonCore.postnikovCommonClassFixedStandard_reference_hom
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

def postnikovCommonClassFixedRightNaturality : SquareZero.RelativeWitness
    (postnikovCommonClassStandardGlueProjection R f c d ≫
      postnikovCommonClassFixedZeroBase R f c d hj)
    (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1)
    ((cellPathNonpositiveProjection R (postnikovCommonRightZeroGlueSource R f c d) ≫
      postnikovCommonClassStandardEndpoint R f c d hj) ≫
      postnikovCommonClassFixedZeroMap R f c d hj)
    (postnikovCommonClassFixedNaturalityEndpoint R f c d hj) :=
  PostnikovCommonCore.postnikovCommonClassFixedRightNaturality
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
