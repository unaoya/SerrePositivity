module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonClassTransition

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreClassTransitionWitness
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreSpecialization

/-!
概要：遷移後の class の底変更経路を、元の層を制限した class 標的へ戻す。
方針：二つの底変更射影で両端を同定し、恒等係数同型の逆で経路を移す。
規約：元の二 class・A の係数遷移・P 上の定数射影を保持。使われ方：標準 class との比較。
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
  (d : PostnikovCommonLayerInverse R f c) {j : ℕ} {hj : j ≤ i}
  (e : PostnikovZeroLayerInverse R 1 f j i hj)

def postnikovCommonClassTransitionTarget : postnikovCommonRightZeroGlueSource R f c d ⟶
    SquareZero.algebra (postnikovCommonClassBase R f c d)
      (postnikovCommonClassTransitionLayer R f c d hj) :=
  PostnikovCommonCore.postnikovCommonClassTransitionTarget
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

def postnikovCommonClassTransitionSource : postnikovCommonRightZeroGlueSource R f c d ⟶
    SquareZero.algebra (postnikovCommonClassBase R f c d)
      (postnikovCommonClassTransitionLayer R f c d hj) :=
  PostnikovCommonCore.postnikovCommonClassTransitionSource
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

lemma postnikovCommonClassTransitionTarget_projection :
    postnikovCommonClassTransitionTarget R f c d (hj := hj) ≫ SquareZero.projection _ _ =
      postnikovCommonRightZeroGlueProjection R f c d :=
  PostnikovCommonCore.postnikovCommonClassTransitionTarget_projection
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

lemma postnikovCommonClassTransitionSource_projection :
    postnikovCommonClassTransitionSource R f c d (hj := hj) ≫ SquareZero.projection _ _ =
      postnikovCommonRightZeroGlueProjection R f c d :=
  PostnikovCommonCore.postnikovCommonClassTransitionSource_projection
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

lemma postnikovCommonClassTransitionTarget_zero :
    postnikovCommonClassTransitionTarget R f c d (hj := hj) ≫
      postnikovCommonClassTransitionToZero R f c d hj =
        postnikovCommonClassRetractTarget R f c d (hj := hj) :=
  PostnikovCommonCore.postnikovCommonClassTransitionTarget_zero
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

lemma postnikovCommonClassTransitionSource_zero :
    postnikovCommonClassTransitionSource R f c d (hj := hj) ≫
      postnikovCommonClassTransitionToZero R f c d hj =
        postnikovCommonClassRetractSource R f c d (hj := hj) :=
  PostnikovCommonCore.postnikovCommonClassTransitionSource_zero
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

lemma postnikovCommonClassRetractLeft_eq : postnikovCommonClassRetractLeft R f c d e =
    postnikovCommonClassTransitionTarget R f c d (hj := hj) ≫
      (postnikovCommonClassTransitionIso R f c d hj).hom :=
  PostnikovCommonCore.postnikovCommonClassRetractLeft_eq
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj) (e := e)

lemma postnikovCommonClassRetractRight_eq : postnikovCommonClassRetractRight R f c d e =
    postnikovCommonClassTransitionSource R f c d (hj := hj) ≫
      (postnikovCommonClassTransitionIso R f c d hj).hom :=
  PostnikovCommonCore.postnikovCommonClassRetractRight_eq
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj) (e := e)

/-- 遷移後の元の二 class の像を、P に相対的な実乗法的経路で結ぶ。 -/
def postnikovCommonClassTransitionWitness : Path.Witness R
    (postnikovCommonClassTransitionTarget R f c d (hj := hj))
    (postnikovCommonClassTransitionSource R f c d (hj := hj)) :=
  PostnikovCommonCore.postnikovCommonClassTransitionWitness
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj) (e := e)

lemma postnikovCommonClassTransitionWitness_projection :
    (postnikovCommonClassTransitionWitness R f c d e).hom ≫ Path.map R (SquareZero.projection _ _) =
      postnikovCommonRightZeroGlueProjection R f c d ≫
        Path.diagonal R (postnikovCommonClassBase R f c d) :=
  PostnikovCommonCore.postnikovCommonClassTransitionWitness_projection
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj) (e := e)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
