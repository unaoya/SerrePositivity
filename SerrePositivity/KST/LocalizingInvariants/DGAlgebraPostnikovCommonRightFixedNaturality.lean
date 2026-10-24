module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraCellFixedNonpositiveNaturality
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightFixedBasePath

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightFixedNaturality
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreSpecialization

/-!
概要：元の指定右経路の cell 反映と B の遷移を、元の class 上の二重経路で比較する。
方針：非正次数源上の自然性正方形を実 class 射で後合成する。
規約：左右の cell 合成比較と全底経路を保持。使われ方：新 Γ の右三角形。
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

def postnikovCommonRightFixedPostClassWitness : Path.Witness R
    ((cellPathNonpositiveComparison R (postnikovCommonRightBase R f c d) ≫
      cellResolutionMap R (postnikovMap R (B.transition hj).hom 1)) ≫
      postnikovCellClass R (B.obj j).obj 1 (by omega))
    ((cellPathNonpositiveComparison R (postnikovCommonRightDenBase R f c d) ≫
      cellResolutionMap R (postnikovMap R (B.transition hj).hom 1)) ≫
      postnikovCellClass R (B.obj j).obj 1 (by omega)) :=
  PostnikovCommonCore.postnikovCommonRightFixedPostClassWitness
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

def postnikovCommonRightFixedMappedClassWitness : Path.Witness R
    (cellPathNonpositiveComparison R (postnikovCommonRightBase R f c d ≫
      postnikovMap R (B.transition hj).hom 1) ≫ postnikovCellClass R (B.obj j).obj 1 (by omega))
    (cellPathNonpositiveComparison R (postnikovCommonRightDenBase R f c d ≫
      postnikovMap R (B.transition hj).hom 1) ≫ postnikovCellClass R (B.obj j).obj 1 (by omega)) :=
  PostnikovCommonCore.postnikovCommonRightFixedMappedClassWitness
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

def postnikovCommonRightFixedClassNaturalitySquare : Path.Witness R
    (postnikovCommonRightFixedPostClassWitness R f c d hj).hom
    (postnikovCommonRightFixedMappedClassWitness R f c d hj).hom :=
  PostnikovCommonCore.postnikovCommonRightFixedClassNaturalitySquare
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

lemma postnikovCommonRightFixedClassNaturalitySquare_source_trace :
    (postnikovCommonRightFixedClassNaturalitySquare R f c d hj).hom ≫
      Path.map R (Path.source R (postnikovDerivationTarget R (B.obj j).obj 1 (by omega))) =
    (cellFixedNonpositiveToDoubleCell R (postnikovCommonClassBase R f c d) ≫
      (cellResolutionMapCompositionWitness R (postnikovCommonRightBase R f c d)
        (postnikovMap R (B.transition hj).hom 1)).hom) ≫
      Path.map R (postnikovCellClass R (B.obj j).obj 1 (by omega)) :=
  PostnikovCommonCore.postnikovCommonRightFixedClassNaturalitySquare_source_trace
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

lemma postnikovCommonRightFixedClassNaturalitySquare_target_trace :
    (postnikovCommonRightFixedClassNaturalitySquare R f c d hj).hom ≫
      Path.map R (Path.target R (postnikovDerivationTarget R (B.obj j).obj 1 (by omega))) =
    (cellFixedNonpositiveToDoubleCell R (postnikovCommonClassBase R f c d) ≫
      (cellResolutionMapCompositionWitness R (postnikovCommonRightDenBase R f c d)
        (postnikovMap R (B.transition hj).hom 1)).hom) ≫
      Path.map R (postnikovCellClass R (B.obj j).obj 1 (by omega)) :=
  PostnikovCommonCore.postnikovCommonRightFixedClassNaturalitySquare_target_trace
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

lemma postnikovCommonRightFixedClassNaturalitySquare_base_trace :
    (postnikovCommonRightFixedClassNaturalitySquare R f c d hj).hom ≫
      Path.map R (Path.map R (SquareZero.projection (postnikov R (B.obj j).obj 1)
        (postnikovShiftedLayerBimodule R (B.obj j).obj 1 (by omega) 1))) =
    (postnikovCommonRightCellProjection R f c d ≫
      ((postnikovCommonRightBasePath R f c d).postcomp
        (postnikovMap R (B.transition hj).hom 1)).hom) ≫
      Path.diagonal R (Path.algebra R (postnikov R (B.obj j).obj 1)) :=
  PostnikovCommonCore.postnikovCommonRightFixedClassNaturalitySquare_base_trace
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
