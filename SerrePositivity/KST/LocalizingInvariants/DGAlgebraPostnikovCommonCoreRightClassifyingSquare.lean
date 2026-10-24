module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCellPathNaturalitySquare
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightFixedNaturality

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
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
open ProExcision
variable (R : Type u) [CommRing R] {n : ℤ} (hn : 0 ≤ n)
  {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (lowerFunctor R n hn)) i m hi)
  (d : PostnikovCommonLayerInverse R hn f c) {j : ℕ} (hj : j ≤ i)

attribute [local instance] PostnikovRoofZeroSpan.refined_source_nonpositive
  PostnikovRoofZeroSpan.refined_target_nonpositive

def postnikovCommonRightClassifyingSquare : Path.Witness R
    (cellAugmentation R (postnikovCommonRightCellSource R hn f c d) ≫
      (postnikovCommonRightFixedCellClassWitness R hn f c d).hom ≫
      Path.map R (postnikovDerivationTargetMap R (B.transition hj).hom n hn))
    (cellAugmentation R (postnikovCommonRightCellSource R hn f c d) ≫
      (postnikovCommonRightFixedMappedClassWitness R hn f c d hj).hom) :=
  postnikovCellClassPathNaturalitySquare R (B.obj i).obj (B.obj j).obj
    (postnikovCommonClassBase R hn f c d) n hn
    (postnikovCommonRightBasePath R hn f c d) (B.transition hj).hom

lemma postnikovCommonRightClassifyingSquare_source_trace :
    (postnikovCommonRightClassifyingSquare R hn f c d hj).hom ≫
      Path.map R (Path.source R (postnikovDerivationTarget R (B.obj j).obj n hn)) =
    cellAugmentation R (postnikovCommonRightCellSource R hn f c d) ≫
      ((postnikovCellClassOverNaturalityWitness R (B.obj i).obj (B.obj j).obj
        (postnikovCommonClassBase R hn f c d) n hn
        (postnikovCommonRightBase R hn f c d) (B.transition hj).hom).precompNonpositiveCell R).hom :=
  postnikovCellClassPathNaturalitySquare_source_trace R _ _ _ _ _ _ _

lemma postnikovCommonRightClassifyingSquare_target_trace :
    (postnikovCommonRightClassifyingSquare R hn f c d hj).hom ≫
      Path.map R (Path.target R (postnikovDerivationTarget R (B.obj j).obj n hn)) =
    cellAugmentation R (postnikovCommonRightCellSource R hn f c d) ≫
      ((postnikovCellClassOverNaturalityWitness R (B.obj i).obj (B.obj j).obj
        (postnikovCommonClassBase R hn f c d) n hn
        (postnikovCommonRightDenBase R hn f c d) (B.transition hj).hom).precompNonpositiveCell
        R).hom :=
  postnikovCellClassPathNaturalitySquare_target_trace R _ _ _ _ _ _ _

lemma postnikovCommonRightClassifyingSquare_base_trace :
    (postnikovCommonRightClassifyingSquare R hn f c d hj).hom ≫
      Path.map R (Path.map R (SquareZero.projection (postnikov R (B.obj j).obj n)
        (postnikovShiftedLayerBimodule R (B.obj j).obj n hn 1))) =
    cellAugmentation R (postnikovCommonRightCellSource R hn f c d) ≫
      ((postnikovCommonRightCellProjection R hn f c d ≫
        ((postnikovCommonRightBasePath R hn f c d).postcomp
          (postnikovMap R (B.transition hj).hom n)).hom) ≫
        Path.diagonal R (Path.algebra R (postnikov R (B.obj j).obj n))) :=
  postnikovCellClassPathNaturalitySquare_base_trace R _ _ _ _ _ _ _

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
