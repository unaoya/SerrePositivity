module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCellFactorizationDirectImage
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightDenCompositeZero

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightDenDirectData
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreSpecialization

/-!
概要：元の分母段から j への直接 B 遷移と、その二段因子分解の係数表示を固定する。
方針：塔の厳密な合成式と、元の係数表示の同型を使う。
規約：元の B 遷移そのものを保持。使われ方：分母の直接自然性と二段合成の実比較。
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

def postnikovCommonRightDenDirectMap : (B.obj d.zero.stage).obj ⟶ (B.obj j).obj :=
  PostnikovCommonCore.postnikovCommonRightDenDirectMap
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

lemma postnikovCommonRightDenDirect_factorization :
    (B.transition (d.zero.inverse_le.trans d.zero.stage_le)).hom ≫ (B.transition hj).hom =
      postnikovCommonRightDenDirectMap R f c d hj :=
  PostnikovCommonCore.postnikovCommonRightDenDirect_factorization
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

def postnikovCommonRightDenDirectImageIso :=
  PostnikovCommonCore.postnikovCommonRightDenDirectImageIso
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

def postnikovCommonRightDenDirectToZero :=
  PostnikovCommonCore.postnikovCommonRightDenDirectToZero
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
