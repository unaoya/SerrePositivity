module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonClassStandard

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreClassStandardZeroGlue
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreSpecialization

/-!
概要：遷移後の係数像と A の標準 class の二経路を、同じ非正次数共通源上で貼り合わせる。
方針：零標的へ移して反転・合成し、次数零の底への経路は定数であることを用いる。
規約：元の P への各次数全射準同型を保持。使われ方：標準 class への実相対比較。
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

abbrev postnikovCommonClassStandardGlueSource :=
  PostnikovCommonCore.postnikovCommonClassStandardGlueSource
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

def postnikovCommonClassStandardGlueProjection :=
  PostnikovCommonCore.postnikovCommonClassStandardGlueProjection
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

lemma postnikovCommonClassStandardGlueProjection_quasiIso :
    QuasiIso (postnikovCommonClassStandardGlueProjection R f c d).hom :=
  PostnikovCommonCore.postnikovCommonClassStandardGlueProjection_quasiIso
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

lemma postnikovCommonClassStandardGlueProjection_surjective (n : ℤ) :
    Function.Surjective ((postnikovCommonClassStandardGlueProjection R f c d).hom.f n) :=
  PostnikovCommonCore.postnikovCommonClassStandardGlueProjection_surjective
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (degree := n)

def postnikovCommonClassStandardGlueLeft :=
  PostnikovCommonCore.postnikovCommonClassStandardGlueLeft
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

def postnikovCommonClassStandardGlueRight :=
  PostnikovCommonCore.postnikovCommonClassStandardGlueRight
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

lemma postnikovCommonClassStandardGlueLeft_projection :
    postnikovCommonClassStandardGlueLeft R f c d (hj := hj) ≫ SquareZero.projection _ _ =
      postnikovCommonClassStandardGlueProjection R f c d :=
  PostnikovCommonCore.postnikovCommonClassStandardGlueLeft_projection
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

lemma postnikovCommonClassStandardGlueRight_projection :
    postnikovCommonClassStandardGlueRight R f c d (hj := hj) ≫ SquareZero.projection _ _ =
      postnikovCommonClassStandardGlueProjection R f c d :=
  PostnikovCommonCore.postnikovCommonClassStandardGlueRight_projection
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

def postnikovCommonClassStandardZeroGlueWitness : Path.Witness R
    (postnikovCommonClassStandardGlueLeft R f c d (hj := hj) ≫
      postnikovCommonClassTransitionToZero R f c d hj)
    (postnikovCommonClassStandardGlueRight R f c d (hj := hj) ≫
      postnikovCommonClassTransitionToZero R f c d hj) :=
  PostnikovCommonCore.postnikovCommonClassStandardZeroGlueWitness
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj) (e := e)

lemma postnikovCommonClassStandardZeroGlueWitness_projection :
    (postnikovCommonClassStandardZeroGlueWitness R f c d e).hom ≫
      Path.map R (SquareZero.projection _ _) =
        (postnikovCommonClassStandardGlueProjection R f c d ≫
          (postnikovCommonClassRetractBase R f c d (hj := hj) ≫
            postnikovTransition R (A.obj j).obj 1 0 (by omega))) ≫
              Path.diagonal R (postnikov R (A.obj j).obj 0) :=
  PostnikovCommonCore.postnikovCommonClassStandardZeroGlueWitness_projection
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj) (e := e)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
