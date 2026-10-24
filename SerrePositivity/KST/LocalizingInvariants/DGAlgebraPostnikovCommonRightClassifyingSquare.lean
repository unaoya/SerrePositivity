module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCellPathNaturalitySquare
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightFixedNaturality

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightClassifyingSquare
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreSpecialization

/-!
概要：指定右経路の class と B 遷移の自然性を、元の四辺を持つ実二重経路で比較する。
方針：任意底経路に沿う classifying 自然性正方形を、元の c の右経路へ適用する。
規約：左右の元の class 自然性と全底経路を保持。使われ方：新 Γ の実右三角形。
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

def postnikovCommonRightClassifyingSquare : Path.Witness R
    (cellAugmentation R (postnikovCommonRightCellSource R f c d) ≫
      (postnikovCommonRightFixedCellClassWitness R f c d).hom ≫
      Path.map R (postnikovDerivationTargetMap R (B.transition hj).hom 1 (by omega)))
    (cellAugmentation R (postnikovCommonRightCellSource R f c d) ≫
      (postnikovCommonRightFixedMappedClassWitness R f c d hj).hom) :=
  PostnikovCommonCore.postnikovCommonRightClassifyingSquare
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

lemma postnikovCommonRightClassifyingSquare_source_trace :
    (postnikovCommonRightClassifyingSquare R f c d hj).hom ≫
      Path.map R (Path.source R (postnikovDerivationTarget R (B.obj j).obj 1 (by omega))) =
    cellAugmentation R (postnikovCommonRightCellSource R f c d) ≫
      ((postnikovCellClassOverNaturalityWitness R (B.obj i).obj (B.obj j).obj
        (postnikovCommonClassBase R f c d) 1 (by omega)
        (postnikovCommonRightBase R f c d) (B.transition hj).hom).precompNonpositiveCell R).hom :=
  PostnikovCommonCore.postnikovCommonRightClassifyingSquare_source_trace
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

lemma postnikovCommonRightClassifyingSquare_target_trace :
    (postnikovCommonRightClassifyingSquare R f c d hj).hom ≫
      Path.map R (Path.target R (postnikovDerivationTarget R (B.obj j).obj 1 (by omega))) =
    cellAugmentation R (postnikovCommonRightCellSource R f c d) ≫
      ((postnikovCellClassOverNaturalityWitness R (B.obj i).obj (B.obj j).obj
        (postnikovCommonClassBase R f c d) 1 (by omega)
        (postnikovCommonRightDenBase R f c d) (B.transition hj).hom).precompNonpositiveCell
        R).hom :=
  PostnikovCommonCore.postnikovCommonRightClassifyingSquare_target_trace
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

lemma postnikovCommonRightClassifyingSquare_base_trace :
    (postnikovCommonRightClassifyingSquare R f c d hj).hom ≫
      Path.map R (Path.map R (SquareZero.projection (postnikov R (B.obj j).obj 1)
        (postnikovShiftedLayerBimodule R (B.obj j).obj 1 (by omega) 1))) =
    cellAugmentation R (postnikovCommonRightCellSource R f c d) ≫
      ((postnikovCommonRightCellProjection R f c d ≫
        ((postnikovCommonRightBasePath R f c d).postcomp
          (postnikovMap R (B.transition hj).hom 1)).hom) ≫
        Path.diagonal R (Path.algebra R (postnikov R (B.obj j).obj 1))) :=
  PostnikovCommonCore.postnikovCommonRightClassifyingSquare_base_trace
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
