module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCellOverClassSquareOriginal
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonClassStandard

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreClassStandardSquare
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreSpecialization

/-!
概要：共通底での二重比較の基準経路を、Γ 構成の元の標準 class 経路へ接続する。
方針：元の非正次数共通源から二重 cell 源への射を持ち上げ、augmentation 自然性を使う。
規約：基準経路を選び直さず、全経路の厳密一致を保つ。使われ方：Γ の実三角形。
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
  (d : PostnikovCommonLayerInverse R f c) {j : ℕ} (hj : j ≤ i)

def postnikovCommonStandardToDoubleCell : postnikovCommonRightZeroGlueSource R f c d ⟶
    cellResolution R (cellResolution R (postnikovCommonClassBase R f c d)) :=
  PostnikovCommonCore.postnikovCommonStandardToDoubleCell
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

def postnikovCommonStandardToTripleCell :
    cellResolution R (postnikovCommonRightZeroGlueSource R f c d) ⟶
      cellResolution R (cellResolution R (cellResolution R (postnikovCommonClassBase R f c d))) :=
  PostnikovCommonCore.postnikovCommonStandardToTripleCell
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

lemma postnikovCommonStandardToTripleCell_augmentation :
    postnikovCommonStandardToTripleCell R f c d ≫
      cellAugmentation R (cellResolution R (cellResolution R (postnikovCommonClassBase R f c d))) =
    cellAugmentation R (postnikovCommonRightZeroGlueSource R f c d) ≫
      postnikovCommonStandardToDoubleCell R f c d :=
  PostnikovCommonCore.postnikovCommonStandardToTripleCell_augmentation
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

lemma postnikovCommonClassStandardSquare_original :
    postnikovCommonStandardToTripleCell R f c d ≫
      (postnikovCellOverCommonComparison R (A.obj i).obj (A.obj j).obj
        (postnikovCommonClassBase R f c d) 1 (by omega)
        (postnikovOneRoofRefine R f c d.zero.source_le).roof.numerator (A.transition hj).hom
        (postnikovCellLiftOverNaturalityWitness R (A.obj i).obj (A.obj j).obj
          (postnikovCommonClassBase R f c d) 1 (by omega)
          (postnikovOneRoofRefine R f c d.zero.source_le).roof.numerator (A.transition hj).hom)
        (postnikovCellOverNaturality_relative R (A.obj i).obj (A.obj j).obj
          (postnikovCommonClassBase R f c d) 1 (by omega)
          (postnikovOneRoofRefine R f c d.zero.source_le).roof.numerator
          (A.transition hj).hom)).hom =
    cellAugmentation R (postnikovCommonRightZeroGlueSource R f c d) ≫
      (postnikovCommonClassStandardWitness R f c d hj).hom :=
  PostnikovCommonCore.postnikovCommonClassStandardSquare_original
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
