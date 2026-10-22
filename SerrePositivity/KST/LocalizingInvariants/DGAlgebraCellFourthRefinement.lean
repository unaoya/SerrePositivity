module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraCellFixedNonpositiveNaturality
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCellFactorizationTarget

/-!
概要：既存の非正次数 cell 細分から、四重 cell 源へ元の射影を保つ射を作る。
方針：五重 cell の connective cover から一段だけ augmentation を施す。
規約：正次数での全射性は要求しない。使われ方：二因子分解比較の Γ 源への移送。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (P : Mon (Complex R))

def cellFixedNonpositiveToFourthCell : cellPathNonpositiveSource R P ⟶
    cellResolution R (cellResolution R (cellResolution R (cellResolution R P))) :=
  connectiveCoverInclusion R _ ≫
    iteratedCellAugmentation R
      (cellResolution R (cellResolution R (cellResolution R (cellResolution R P)))) 1

lemma cellFixedNonpositiveToFourthCell_projection :
    cellFixedNonpositiveToFourthCell R P ≫ postnikovCellFactorizationProjection R P =
      cellPathNonpositiveProjection R P := by
  simp only [cellFixedNonpositiveToFourthCell, postnikovCellFactorizationProjection,
    cellPathNonpositiveProjection, iteratedCellAugmentation, iteratedCellResolution,
    Category.assoc, Category.comp_id]
  exact Category.assoc _ _ _

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
