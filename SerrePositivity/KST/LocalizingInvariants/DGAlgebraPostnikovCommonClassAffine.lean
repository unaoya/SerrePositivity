module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonClassStandardZeroGlue
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeWitnessPrecomp

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreClassAffine
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreSpecialization

/-!
概要：遷移比較と標準 class 比較を、同じ共通底上で直接 affine 合成する。
方針：既存の二経路を相対証人へ束ね、その逆と合成を元の貼合せ源へ前合成する。
規約：旧 cellComp との一致は仮定しない。使われ方：元の class 経路の差の明示。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Preadditive
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (postnikovFunctor R 1)) i m hi)
  (d : PostnikovCommonLayerInverse R f c) {j : ℕ} {hj : j ≤ i}
  (e : PostnikovZeroLayerInverse R 1 f j i hj)

def postnikovCommonClassTransitionRelative : SquareZero.RelativeWitness
    (postnikovCommonRightZeroGlueProjection R f c d)
    (postnikovCommonClassTransitionLayer R f c d hj)
    (postnikovCommonClassTransitionTarget R f c d (hj := hj))
    (postnikovCommonClassTransitionSource R f c d (hj := hj)) :=
  PostnikovCommonCore.postnikovCommonClassTransitionRelative
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj) (e := e)

def postnikovCommonClassStandardRelative : SquareZero.RelativeWitness
    (postnikovCommonRightZeroGlueProjection R f c d)
    (postnikovCommonClassTransitionLayer R f c d hj)
    (postnikovCommonClassTransitionTarget R f c d (hj := hj))
    (postnikovCommonClassStandardEndpoint R f c d hj) :=
  PostnikovCommonCore.postnikovCommonClassStandardRelative
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

def postnikovCommonClassAffineRelative : SquareZero.RelativeWitness
    (postnikovCommonRightZeroGlueProjection R f c d)
    (postnikovCommonClassTransitionLayer R f c d hj)
    (postnikovCommonClassTransitionSource R f c d (hj := hj))
    (postnikovCommonClassStandardEndpoint R f c d hj) :=
  PostnikovCommonCore.postnikovCommonClassAffineRelative
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj) (e := e)

def postnikovCommonClassAffineGlueRelative : SquareZero.RelativeWitness
    (postnikovCommonClassStandardGlueProjection R f c d)
    (postnikovCommonClassTransitionLayer R f c d hj)
    (postnikovCommonClassStandardGlueLeft R f c d (hj := hj))
    (postnikovCommonClassStandardGlueRight R f c d (hj := hj)) :=
  PostnikovCommonCore.postnikovCommonClassAffineGlueRelative
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj) (e := e)

lemma postnikovCommonClassAffineRelative_hom_linear :
    (postnikovCommonClassAffineRelative R f c d e).hom.hom =
      (postnikovCommonClassTransitionSource R f c d (hj := hj) ≫ Path.diagonal R _).hom -
        (postnikovCommonClassTransitionWitness R f c d e).hom.hom +
        (postnikovCommonClassStandardWitness R f c d hj).hom.hom :=
  PostnikovCommonCore.postnikovCommonClassAffineRelative_hom_linear
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj) (e := e)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
