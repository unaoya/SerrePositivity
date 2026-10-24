module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonClassRetractBase
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCellClassOverImage
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovClassBaseZeroIso

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreClassTransition
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreSpecialization

/-!
概要：遷移後の元の底の class 標的と、元の A の層遷移の係数射を構成する。
方針：元の class の底変更係数を使い、零底自然性を対角直和の二成分で照合する。
規約：元の分子・遷移と係数を保持。使われ方：底変更で戻した経路の両端同定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (postnikovFunctor R 1)) i m hi)
  (d : PostnikovCommonLayerInverse R f c) {j : ℕ} (hj : j ≤ i)

abbrev postnikovCommonClassTransitionLayer :=
  PostnikovCommonCore.postnikovCommonClassTransitionLayer
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

def postnikovCommonClassTransitionCoefficient :
    postnikovOneRoofShiftedNumeratorLayer R f
      (postnikovOneRoofRefine R f c d.zero.source_le) 1 ⟶
        postnikovCommonClassTransitionLayer R f c d hj :=
  PostnikovCommonCore.postnikovCommonClassTransitionCoefficient
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

def postnikovCommonClassTransitionMap :
    SquareZero.algebra (postnikovCommonClassBase R f c d)
      (postnikovOneRoofShiftedNumeratorLayer R f
        (postnikovOneRoofRefine R f c d.zero.source_le) 1) ⟶
    SquareZero.algebra (postnikovCommonClassBase R f c d)
      (postnikovCommonClassTransitionLayer R f c d hj) :=
  PostnikovCommonCore.postnikovCommonClassTransitionMap
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

def postnikovCommonClassTransitionToZero :
    SquareZero.algebra (postnikovCommonClassBase R f c d)
      (postnikovCommonClassTransitionLayer R f c d hj) ⟶
    postnikovZeroClassTarget R (A.obj j).obj 1 1 :=
  PostnikovCommonCore.postnikovCommonClassTransitionToZero
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

def postnikovCommonClassTransitionIso :
    SquareZero.algebra (postnikovCommonClassBase R f c d)
      (postnikovCommonClassTransitionLayer R f c d hj) ≅
    SquareZero.algebra (postnikovCommonClassBase R f c d)
      (bimoduleRestrict (postnikovCommonClassRetractBase R f c d (hj := hj) ≫
        postnikovTransition R (A.obj j).obj 1 0 (by omega))
          (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (A.obj j).obj 1) 1)) :=
  PostnikovCommonCore.postnikovCommonClassTransitionIso
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

lemma postnikovCommonClassTransitionToZero_projection :
    postnikovCommonClassTransitionToZero R f c d hj ≫ SquareZero.projection _ _ =
      SquareZero.projection _ _ ≫ (postnikovCommonClassRetractBase R f c d (hj := hj) ≫
        postnikovTransition R (A.obj j).obj 1 0 (by omega)) :=
  PostnikovCommonCore.postnikovCommonClassTransitionToZero_projection
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

lemma postnikovCommonClassTransitionToZero_hom :
    (postnikovCommonClassTransitionToZero R f c d hj).hom =
      biprod.map ((postnikovCommonClassRetractBase R f c d (hj := hj)) ≫
        postnikovTransition R (A.obj j).obj 1 0 (by omega)).hom
          (𝟙 ((postnikovLayer R (A.obj j).obj 1)⟦(1 : ℤ)⟧)) :=
  PostnikovCommonCore.postnikovCommonClassTransitionToZero_hom
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

lemma postnikovCommonClassTransition_zero : postnikovCommonClassTransitionMap R f c d hj ≫
    postnikovCommonClassTransitionToZero R f c d hj = postnikovCommonNumeratorToZero R f c d ≫
      postnikovZeroClassMap R 1 1 (A.transition hj).hom :=
  PostnikovCommonCore.postnikovCommonClassTransition_zero
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
