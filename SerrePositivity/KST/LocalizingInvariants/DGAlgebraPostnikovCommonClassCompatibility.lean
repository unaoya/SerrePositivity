module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonClassStandardZeroGlue
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovClassBaseZeroWitness

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreClassCompatibility
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreSpecialization

/-!
概要：細分後の係数逆で移した源 class と、元の低い段の標準 class の実相対経路。
方針：零標的で貼り合わせた経路を、元の class 標的へ実底変更で戻す。
規約：元の係数逆・遷移・両 class と次数全射準同型の源射影を保持。使われ方：二切断逆。
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

def postnikovCommonClassCompatibilityCoefficient :
    postnikovOneRoofShiftedDenominatorLayer R f
      (postnikovOneRoofRefine R f c d.zero.source_le) 1 ⟶
        postnikovCommonClassTransitionLayer R f c d hj :=
  PostnikovCommonCore.postnikovCommonClassCompatibilityCoefficient
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

def postnikovCommonClassCompatibilityToCell : postnikovCommonClassStandardGlueSource R f c d ⟶
    cellResolution R (postnikovCommonClassBase R f c d) :=
  PostnikovCommonCore.postnikovCommonClassCompatibilityToCell
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

lemma postnikovCommonClassCompatibilityToCell_projection :
    postnikovCommonClassCompatibilityToCell R f c d ≫
      cellAugmentation R (postnikovCommonClassBase R f c d) =
        postnikovCommonClassStandardGlueProjection R f c d :=
  PostnikovCommonCore.postnikovCommonClassCompatibilityToCell_projection
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

lemma postnikovCommonClassStandardGlueLeft_eq :
    postnikovCommonClassStandardGlueLeft R f c d (hj := hj) =
      postnikovCommonClassCompatibilityToCell R f c d ≫
        postnikovCellClassOver R (B.obj d.zero.stage).obj (postnikovCommonClassBase R f c d)
          1 (by omega) (postnikovOneRoofRefine R f c d.zero.source_le).roof.denominator ≫
            SquareZero.coefficientMap (postnikovCommonClassBase R f c d)
              (postnikovCommonClassCompatibilityCoefficient R f c d (hj := hj)) :=
  PostnikovCommonCore.postnikovCommonClassStandardGlueLeft_eq
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

lemma postnikovCommonClassStandardGlueRight_eq :
    postnikovCommonClassStandardGlueRight R f c d (hj := hj) =
      postnikovCommonClassCompatibilityToCell R f c d ≫
        postnikovCellClassOver R (A.obj j).obj (postnikovCommonClassBase R f c d) 1 (by omega)
          (postnikovCommonClassRetractBase R f c d (hj := hj)) :=
  PostnikovCommonCore.postnikovCommonClassStandardGlueRight_eq
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

/-- 原仮定から構成した係数逆の class 整合。経路存在は追加入力しない。 -/
def postnikovCommonClassCompatibilityWitness : Path.Witness R
    (postnikovCommonClassStandardGlueLeft R f c d (hj := hj))
    (postnikovCommonClassStandardGlueRight R f c d (hj := hj)) :=
  PostnikovCommonCore.postnikovCommonClassCompatibilityWitness
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj) (e := e)

lemma postnikovCommonClassCompatibilityWitness_projection :
    (postnikovCommonClassCompatibilityWitness R f c d e).hom ≫
      Path.map R (SquareZero.projection _ _) =
        postnikovCommonClassStandardGlueProjection R f c d ≫
          Path.diagonal R (postnikovCommonClassBase R f c d) :=
  PostnikovCommonCore.postnikovCommonClassCompatibilityWitness_projection
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj) (e := e)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
