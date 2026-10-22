module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCellClassOverNaturality
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroCellWitnessSquare
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeSquareBaseChange
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeWitnessPrecomp

/-!
概要：元の Postnikov 自然性経路と、同じ摂動射上の別経路を class 二重経路で比較する。
方針：実摂動射の全射準同型性を使い、元の底射の合成式で定数底を同定する。
規約：追加の class 二重経路は入力しない。使われ方：共通底 P 上の自然性の整合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (B C P : Mon (Complex R))
  [B.X.IsStrictlyLE 0] [C.X.IsStrictlyLE 0]
  (n : ℤ) (hn : 0 ≤ n) (b : P ⟶ postnikov R B n) (f : B ⟶ C)

/-- 構成した二重充填で一回増える cell augmentation を含む、元の P への射。 -/
def postnikovCellOverComparisonProjection : cellResolution R (cellResolution R
    (cellResolution R P)) ⟶ P :=
  cellAugmentation R (cellResolution R (cellResolution R P)) ≫
    cellAugmentation R (cellResolution R P) ≫ cellAugmentation R P

variable (w : Path.Witness R
    (cellAugmentation R (cellResolution R P) ≫ postnikovCellLiftOverSource R B C P n hn b f)
    (cellAugmentation R (cellResolution R P) ≫ postnikovCellLiftOverTarget R B C P n hn b f))
  (hw : w.hom ≫ Path.map R (postnikovPerturbedProjection R C n hn) =
    ((cellAugmentation R (cellResolution R P) ≫
      postnikovCellLiftOverSource R B C P n hn b f) ≫ postnikovPerturbedProjection R C n hn) ≫
        Path.diagonal R (postnikov R C n))

lemma postnikovCellOverComparison_base :
    cellAugmentation R (cellResolution R (cellResolution R P)) ≫
      (cellAugmentation R (cellResolution R P) ≫
        postnikovCellLiftOverSource R B C P n hn b f) ≫
        postnikovPerturbedProjection R C n hn =
    postnikovCellOverComparisonProjection R P ≫ (b ≫ postnikovMap R f n) := by
  rw [Category.assoc (cellAugmentation R (cellResolution R P))
    (postnikovCellLiftOverSource R B C P n hn b f),
    postnikovCellLiftOverSource_projection]
  simp only [Category.assoc, postnikovCellOverComparisonProjection]

def postnikovCellOverClassComparison : SquareZero.RelativeWitness
    (postnikovCellOverComparisonProjection R P ≫ (b ≫ postnikovMap R f n))
    (postnikovShiftedLayerBimodule R C n hn 1)
    (cellAugmentation R (cellResolution R (cellResolution R P)) ≫
      (cellAugmentation R (cellResolution R P) ≫
        postnikovCellLiftOverSource R B C P n hn b f) ≫ postnikovPerturbedClass R C n hn)
    (cellAugmentation R (cellResolution R (cellResolution R P)) ≫
      (cellAugmentation R (cellResolution R P) ≫
        postnikovCellLiftOverTarget R B C P n hn b f) ≫ postnikovPerturbedClass R C n hn) :=
  (SquareZero.cellClassWitness R (postnikovPerturbedProjection R C n hn) w hw
    (postnikovShiftedLayerBimodule R C n hn 1) (postnikovPerturbedClass R C n hn)
    (postnikovPerturbedClass_projection R C n hn)).rebase
      (postnikovCellOverComparison_base R B C P n hn b f)

lemma postnikovCellOverNaturality_relative :
    (postnikovCellLiftOverNaturalityWitness R B C P n hn b f).hom ≫
      Path.map R (postnikovPerturbedProjection R C n hn) =
    ((cellAugmentation R (cellResolution R P) ≫
      postnikovCellLiftOverSource R B C P n hn b f) ≫ postnikovPerturbedProjection R C n hn) ≫
        Path.diagonal R (postnikov R C n) := by
  rw [Category.assoc (cellAugmentation R (cellResolution R P))
    (postnikovCellLiftOverSource R B C P n hn b f),
    postnikovCellLiftOverSource_projection]
  exact postnikovCellLiftOverNaturalityWitness_relative R B C P n hn b f

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
