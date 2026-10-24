module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoFixedRightDirectClassRestore
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoSourceModelProjections

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSuccessorFixedRightDirectNativeInput

/-!
概要：元の分母相対模型の class と経路を、元の Bⱼ の平方零標的へ送る射を構成する。
方針：係数復元と元の直接 B 遷移を同一視し、元の零切断と source class を保つ。
規約：元の係数と sourceCellMap を保持。使われ方：source 模型ホモトピーの実入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} {f : LevelHom A B}
  {j : ℕ} (d : PostnikovTwoClassInverseData R f j)

abbrev directNativeLayer :=
  PostnikovSuccessorClassInverseData.directNativeLayer
    (R := R) (n := (1 : ℤ)) (hn := by decide) (B := B) (j := j)

def directNativeClassMap : SquareZero.algebra (d.classBase R) (d.denominatorLayer R) ⟶
    postnikovDerivationTarget R (B.obj j).obj 1 (by omega) :=
  PostnikovSuccessorClassInverseData.directNativeClassMap
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma directNativeClassMap_projection : d.directNativeClassMap R ≫
    SquareZero.projection (postnikov R (B.obj j).obj 1) (directNativeLayer (B := B) (j := j) R) =
    SquareZero.projection (d.classBase R) (d.denominatorLayer R) ≫
      postnikovCommonClassRightDenominatorBase R f d.baseInverse d.layerInverse d.target_le :=
  PostnikovSuccessorClassInverseData.directNativeClassMap_projection
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma directNativeClassMap_zero : SquareZero.zeroSection (d.classBase R) (d.denominatorLayer R) ≫
    d.directNativeClassMap R =
    postnikovCommonClassRightDenominatorBase R f d.baseInverse d.layerInverse d.target_le ≫
      SquareZero.zeroSection (postnikov R (B.obj j).obj 1)
        (directNativeLayer (B := B) (j := j) R) :=
  PostnikovSuccessorClassInverseData.directNativeClassMap_zero
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

def directNativeSource :=
  PostnikovSuccessorClassInverseData.directNativeSource
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma sourceClass_directNative : d.sourceClass R ≫ d.directNativeClassMap R =
    d.directNativeSource R ≫ postnikovPerturbedClass R (B.obj j).obj 1 (by omega) :=
  PostnikovSuccessorClassInverseData.sourceClass_directNative
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
