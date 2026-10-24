module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightClassGlue
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovZeroClassMap

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightZeroNaturality
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreSpecialization

/-!
概要：共通右 class 標的への射を、元の A の零 class 標的と f の像で因子分解する。
方針：零底の自然性と元の係数射を、実代数射の二つの対角成分で照合する。
規約：元の分子射と shift 係数を保持。使われ方：後続段の実係数逆で右像を外す。
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
  (d : PostnikovCommonLayerInverse R f c)

lemma postnikovCommonRightZeroBase_source : postnikovCommonRightZeroBase R f c d =
    (postnikovOneRoofRefine R f c d.zero.source_le).roof.numerator ≫
      postnikovTransition R (A.obj i).obj 1 0 (by omega) ≫ postnikovMap R (f.app i).hom 0 :=
  PostnikovCommonCore.postnikovCommonRightZeroBase_source
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

def postnikovCommonNumeratorToZero :
    SquareZero.algebra (postnikovCommonClassBase R f c d)
      (postnikovOneRoofShiftedNumeratorLayer R f
        (postnikovOneRoofRefine R f c d.zero.source_le) 1) ⟶
      postnikovZeroClassTarget R (A.obj i).obj 1 1 :=
  PostnikovCommonCore.postnikovCommonNumeratorToZero
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

lemma postnikovCommonRightNumerator_zero : postnikovCommonRightClassNumeratorMap R f c d ≫
    postnikovCommonRightClassToZero R f c d =
      postnikovCommonNumeratorToZero R f c d ≫ postnikovZeroClassMap R 1 1 (f.app i).hom :=
  PostnikovCommonCore.postnikovCommonRightNumerator_zero
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
