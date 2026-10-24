module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightZeroNaturality
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovZeroClassInverse

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreClassRetract
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreSpecialization

/-!
概要：後続段の実係数逆で右 class 像の経路を戻し、A の遷移後の二 class を比較する。
方針：元の係数逆の厳密な左三角形で f の右像を外し、実経路を同じ代数射で後合成する。
規約：係数逆の源段と比較段を一致させる。使われ方：細分後の class 整合。
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

def postnikovCommonRightRetract : postnikovCommonRightClassTarget R f c d ⟶
    postnikovZeroClassTarget R (A.obj j).obj 1 1 :=
  PostnikovCommonCore.postnikovCommonRightRetract
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj) (e := e)

lemma postnikovCommonRightNumerator_retract : postnikovCommonRightClassNumeratorMap R f c d ≫
    postnikovCommonRightRetract R f c d e = postnikovCommonNumeratorToZero R f c d ≫
      postnikovZeroClassMap R 1 1 (A.transition hj).hom :=
  PostnikovCommonCore.postnikovCommonRightNumerator_retract
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj) (e := e)

lemma postnikovCommonRightRetract_projection : postnikovCommonRightRetract R f c d e ≫
    SquareZero.projection _ _ = SquareZero.projection _ _ ≫
      (postnikovCommonRightZeroBase R f c d ≫ e.base) :=
  PostnikovCommonCore.postnikovCommonRightRetract_projection
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj) (e := e)

def postnikovCommonClassRetractTarget :=
  PostnikovCommonCore.postnikovCommonClassRetractTarget
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

def postnikovCommonClassRetractSource :=
  PostnikovCommonCore.postnikovCommonClassRetractSource
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

lemma postnikovCommonRightGlueTarget_retract : postnikovCommonRightGlueTarget R f c d ≫
    postnikovCommonRightRetract R f c d e = postnikovCommonClassRetractTarget R f c d (hj := hj) :=
  PostnikovCommonCore.postnikovCommonRightGlueTarget_retract
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj) (e := e)

lemma postnikovCommonRightGlueSource_retract : postnikovCommonRightGlueSource R f c d ≫
    postnikovCommonRightRetract R f c d e = postnikovCommonClassRetractSource R f c d (hj := hj) :=
  PostnikovCommonCore.postnikovCommonRightGlueSource_retract
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj) (e := e)

/-- 右像の経路と後続段の実係数逆だけから、A の遷移後の二 class の経路を得る。 -/
def postnikovCommonClassRetractWitness : Path.Witness R
    (postnikovCommonClassRetractTarget R f c d (hj := hj))
    (postnikovCommonClassRetractSource R f c d (hj := hj)) :=
  PostnikovCommonCore.postnikovCommonClassRetractWitness
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj) (e := e)

lemma postnikovCommonClassRetractWitness_projection :
    (postnikovCommonClassRetractWitness R f c d e).hom ≫ Path.map R (SquareZero.projection _ _) =
      postnikovCommonRightZeroGlueProjection R f c d ≫
        (postnikovCommonRightZeroBase R f c d ≫ e.base) ≫
          Path.diagonal R (postnikov R (A.obj j).obj 0) :=
  PostnikovCommonCore.postnikovCommonClassRetractWitness_projection
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj) (e := e)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
