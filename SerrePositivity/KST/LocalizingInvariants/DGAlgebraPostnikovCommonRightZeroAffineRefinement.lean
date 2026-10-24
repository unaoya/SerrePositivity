module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightCompositeZeroIso
public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightAffineRefinement
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeSquareMapOver

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightZeroAffineRefinement
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreSpecialization

/-!
概要：元の Γ 源上の affine 二因子分解比較を、classifying 側の零底係数へ移す。
方針：底を固定する実平方零同型で全二重経路を後合成する。
規約：元の Γ 射影と全経路を保持。使われ方：零底の貼合せ輪郭との実比較。
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

lemma postnikovCommonRightCompositeZeroIso_over :
    (postnikovCommonRightCompositeZeroIso R f c d hj).hom ≫ SquareZero.projection _ _ =
      SquareZero.projection _ _ ≫ 𝟙 (postnikovCommonClassBase R f c d) :=
  PostnikovCommonCore.postnikovCommonRightCompositeZeroIso_over
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

def postnikovCommonRightZeroAffineSource :=
  PostnikovCommonCore.postnikovCommonRightZeroAffineSource
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

def postnikovCommonRightZeroAffineTarget :=
  PostnikovCommonCore.postnikovCommonRightZeroAffineTarget
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

def postnikovCommonRightZeroAffineViaA : SquareZero.RelativeWitness
    (postnikovCommonClassStandardGlueProjection R f c d)
    (postnikovCommonRightClassifyingLayer R f c d hj)
    (postnikovCommonRightZeroAffineSource R f c d hj)
    (postnikovCommonRightZeroAffineTarget R f c d hj) :=
  PostnikovCommonCore.postnikovCommonRightZeroAffineViaA
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

def postnikovCommonRightZeroAffineViaB : SquareZero.RelativeWitness
    (postnikovCommonClassStandardGlueProjection R f c d)
    (postnikovCommonRightClassifyingLayer R f c d hj)
    (postnikovCommonRightZeroAffineSource R f c d hj)
    (postnikovCommonRightZeroAffineTarget R f c d hj) :=
  PostnikovCommonCore.postnikovCommonRightZeroAffineViaB
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

def postnikovCommonRightZeroAffineSquare : SquareZero.RelativeWitnessSquare
    (postnikovCommonRightZeroAffineViaA R f c d hj)
    (postnikovCommonRightZeroAffineViaB R f c d hj) :=
  PostnikovCommonCore.postnikovCommonRightZeroAffineSquare
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

def postnikovCommonRightZeroAffineTransportHomotopy : Path.Witness R
    (SquareZeroExtension.transport (postnikovCommonRightClassifyingLayer R f c d hj)
      (postnikovCommonRightZeroAffineViaA R f c d hj))
    (SquareZeroExtension.transport (postnikovCommonRightClassifyingLayer R f c d hj)
      (postnikovCommonRightZeroAffineViaB R f c d hj)) :=
  PostnikovCommonCore.postnikovCommonRightZeroAffineTransportHomotopy
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
