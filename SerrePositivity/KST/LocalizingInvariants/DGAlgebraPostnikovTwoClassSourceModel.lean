module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoClassModelMaps
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCellHomotopyPullback
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroBaseChangeQuasiIso

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSuccessorClassSourceModel

/-!
概要：二切断逆の共通底の源拡大模型を、元の B の class 模型へ実準同型で比較する。
方針：元の分母と cell 比較の三つの準同型を使い、既存の摂動 class 比較へ接続する。
規約：元の右脚と底の分母を保持。使われ方：元の二切断代数を分母に取る実 roof。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} {f : LevelHom A B}
  {j : ℕ} (d : PostnikovTwoClassInverseData R f j)

def sourceCellMap : d.classSource R ⟶
    cellResolution R (postnikov R (B.obj d.layerInverse.zero.stage).obj 1) :=
  PostnikovSuccessorClassInverseData.sourceCellMap
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma sourceCellMap_quasiIso : QuasiIso (d.sourceCellMap R).hom :=
  PostnikovSuccessorClassInverseData.sourceCellMap_quasiIso
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

abbrev sourceCellModel : Mon (Complex R) :=
  PostnikovSuccessorClassInverseData.sourceCellModel
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

abbrev originalSourceModel : Mon (Complex R) :=
  PostnikovSuccessorClassInverseData.originalSourceModel
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

def sourceToCellModel : d.sourceModel R ⟶ d.sourceCellModel R :=
  PostnikovSuccessorClassInverseData.sourceToCellModel
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma sourceToCellModel_quasiIso : QuasiIso (d.sourceToCellModel R).hom :=
  PostnikovSuccessorClassInverseData.sourceToCellModel_quasiIso
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

def sourceToOriginalModel : d.sourceModel R ⟶ d.originalSourceModel R :=
  PostnikovSuccessorClassInverseData.sourceToOriginalModel
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma sourceToOriginalModel_quasiIso : QuasiIso (d.sourceToOriginalModel R).hom :=
  PostnikovSuccessorClassInverseData.sourceToOriginalModel_quasiIso
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma sourceToOriginalModel_right : d.sourceToOriginalModel R ≫
    HomotopyPullbackModel.right R _ _ = HomotopyPullbackModel.right R _ _ ≫
      (d.lowerBaseInverse R).roof.denominator :=
  PostnikovSuccessorClassInverseData.sourceToOriginalModel_right
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
