module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightCellProjection
public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoFixedRightCompletedOriginalModel

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSuccessorFixedRightDirectSourcePath

/-!
概要：元の直接 B 遷移の source 自然性経路を同じ Γ 上に取り出す。
方針：元の二重 cell 射で前合成し、元の cell 射への厳密な射影式を使う。
規約：元の乗法的 source 経路と一定の底を保持。使われ方：直接模型射の比較。
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

def fixedRightDirectSourcePath :=
  PostnikovSuccessorClassInverseData.fixedRightDirectSourcePath
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma fixedRightDirectSourcePath_source : (d.fixedRightDirectSourcePath R).hom ≫
    Path.source R (postnikovPerturbedExtension R (B.obj j).obj 1 (by omega)) =
    d.sourceCellMap R ≫ postnikovCellLift R (B.obj d.layerInverse.zero.stage).obj 1 (by omega) ≫
      postnikovPerturbedMap R
        (postnikovCommonRightDenDirectMap R f d.baseInverse d.layerInverse d.target_le)
        1 (by omega) :=
  PostnikovSuccessorClassInverseData.fixedRightDirectSourcePath_source
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma fixedRightDirectSourcePath_target : (d.fixedRightDirectSourcePath R).hom ≫
    Path.target R (postnikovPerturbedExtension R (B.obj j).obj 1 (by omega)) =
      d.fixedRightCompletedNativeSource R :=
  PostnikovSuccessorClassInverseData.fixedRightDirectSourcePath_target
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma fixedRightDirectSourcePath_relative : (d.fixedRightDirectSourcePath R).hom ≫
    Path.map R (postnikovPerturbedProjection R (B.obj j).obj 1 (by omega)) =
    (d.classProjection R ≫ postnikovCommonClassRightDenominatorBase R f d.baseInverse
      d.layerInverse d.target_le) ≫ Path.diagonal R (postnikov R (B.obj j).obj 1) :=
  PostnikovSuccessorClassInverseData.fixedRightDirectSourcePath_relative
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma fixedRightDirectSourcePath_class : (d.fixedRightDirectSourcePath R).hom ≫
    Path.map R (postnikovPerturbedClass R (B.obj j).obj 1 (by omega)) =
    postnikovCommonRightImageToSecond R f d.baseInverse d.layerInverse ≫
      (postnikovCellClassOverNaturalityWitness R (B.obj d.layerInverse.zero.stage).obj
        (B.obj j).obj (d.classBase R) 1 (by omega) (d.lowerBaseInverse R).roof.denominator
        (postnikovCommonRightDenDirectMap R f d.baseInverse d.layerInverse d.target_le)).hom :=
  PostnikovSuccessorClassInverseData.fixedRightDirectSourcePath_class
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
