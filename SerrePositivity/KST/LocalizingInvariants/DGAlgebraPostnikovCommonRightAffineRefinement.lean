module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightAffineCompositeSquare
public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightComparisonRefinement
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeSquarePrecomp

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightAffineRefinement
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreSpecialization

/-!
概要：A 遷移と f の二因子分解の affine 比較を、元の Γ の源へ移す。
方針：指定した細分射を前合成し、元の Γ 射影へ等式で移す。
規約：係数は合成射による制限のまま。使われ方：零底の貼合せ比較への次の係数移送。
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

def postnikovCommonRightAffineRefinedSource :=
  PostnikovCommonCore.postnikovCommonRightAffineRefinedSource
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

def postnikovCommonRightAffineRefinedTarget :=
  PostnikovCommonCore.postnikovCommonRightAffineRefinedTarget
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

def postnikovCommonRightAffineRefinedViaA : SquareZero.RelativeWitness
    (postnikovCommonClassStandardGlueProjection R f c d)
    (postnikovCommonRightNaturalityCompositeLayer R f c d hj)
    (postnikovCommonRightAffineRefinedSource R f c d hj)
    (postnikovCommonRightAffineRefinedTarget R f c d hj) :=
  PostnikovCommonCore.postnikovCommonRightAffineRefinedViaA
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

def postnikovCommonRightAffineRefinedViaB : SquareZero.RelativeWitness
    (postnikovCommonClassStandardGlueProjection R f c d)
    (postnikovCommonRightNaturalityCompositeLayer R f c d hj)
    (postnikovCommonRightAffineRefinedSource R f c d hj)
    (postnikovCommonRightAffineRefinedTarget R f c d hj) :=
  PostnikovCommonCore.postnikovCommonRightAffineRefinedViaB
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

/-- 元の Γ 源と射影の上で、二つの affine 合成経路を結ぶ実二重経路。 -/
def postnikovCommonRightAffineRefinedSquare : SquareZero.RelativeWitnessSquare
    (postnikovCommonRightAffineRefinedViaA R f c d hj)
    (postnikovCommonRightAffineRefinedViaB R f c d hj) :=
  PostnikovCommonCore.postnikovCommonRightAffineRefinedSquare
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

def postnikovCommonRightAffineRefinedTransportHomotopy : Path.Witness R
    (SquareZeroExtension.transport (postnikovCommonRightNaturalityCompositeLayer R f c d hj)
      (postnikovCommonRightAffineRefinedViaA R f c d hj))
    (SquareZeroExtension.transport (postnikovCommonRightNaturalityCompositeLayer R f c d hj)
      (postnikovCommonRightAffineRefinedViaB R f c d hj)) :=
  PostnikovCommonCore.postnikovCommonRightAffineRefinedTransportHomotopy
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
