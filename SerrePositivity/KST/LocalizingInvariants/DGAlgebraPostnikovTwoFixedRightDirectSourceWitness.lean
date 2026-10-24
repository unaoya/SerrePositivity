module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoFixedRightDirectNativeInput

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSuccessorFixedRightDirectSourceWitness

/-!
概要：元の直接 source 経路の両端を、元の sourceCellMap と completed source で表示する。
方針：保存済みの両端式を束ね、元の全射と一定底式を保持する。
規約：経路は選び直さない。使われ方：元の相対模型への source ホモトピーの適用。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} {f : LevelHom A B}
  {j : ℕ} (d : PostnikovTwoClassInverseData R f j)

def fixedRightDirectSourceWitness : Path.Witness R (d.directNativeSource R)
    (d.fixedRightCompletedNativeSource R) :=
  PostnikovSuccessorClassInverseData.fixedRightDirectSourceWitness
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma fixedRightDirectSourceWitness_hom : (d.fixedRightDirectSourceWitness R).hom =
    (d.fixedRightDirectSourcePath R).hom :=
  PostnikovSuccessorClassInverseData.fixedRightDirectSourceWitness_hom
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma fixedRightDirectSourceWitness_relative : (d.fixedRightDirectSourceWitness R).hom ≫
    Path.map R (postnikovPerturbedProjection R (B.obj j).obj 1 (by omega)) =
    (d.classProjection R ≫ postnikovCommonClassRightDenominatorBase R f d.baseInverse
      d.layerInverse d.target_le) ≫ Path.diagonal R (postnikov R (B.obj j).obj 1) :=
  PostnikovSuccessorClassInverseData.fixedRightDirectSourceWitness_relative
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma sourceRelativeRight_projection :
    SquareZeroExtension.relativeRight (d.denominatorLayer R) (d.sourceClass R) =
    SquareZeroExtension.relativeLeft (d.denominatorLayer R) (d.sourceClass R) ≫
      d.classProjection R :=
  PostnikovSuccessorClassInverseData.sourceRelativeRight_projection
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma fixedRightDirectSourceWitness_class_relative :
    ((d.fixedRightDirectSourceWitness R).hom ≫
      Path.map R (postnikovPerturbedClass R (B.obj j).obj 1 (by omega))) ≫
      Path.map R (SquareZero.projection (postnikov R (B.obj j).obj 1)
        (directNativeLayer (B := B) (j := j) R)) =
    (d.classProjection R ≫ postnikovCommonClassRightDenominatorBase R f d.baseInverse
      d.layerInverse d.target_le) ≫ Path.diagonal R (postnikov R (B.obj j).obj 1) :=
  PostnikovSuccessorClassInverseData.fixedRightDirectSourceWitness_class_relative
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
