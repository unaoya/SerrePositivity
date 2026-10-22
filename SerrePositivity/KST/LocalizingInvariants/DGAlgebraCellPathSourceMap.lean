module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraCellPathNonpositive

/-!
概要：非正次数共通源から、一重・二重 cell 源への元の比較射を明示する。
方針：同じ反復 augmentation を有限段で因子分解する。
規約：元の源への射影を保持。使われ方：三つの class 経路の共通源への移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R]

def cellPathNonpositiveToCell (A : Mon (Complex R)) :
    cellPathNonpositiveSource R A ⟶ cellResolution R A :=
  connectiveCoverInclusion R _ ≫ iteratedCellAugmentation R (cellResolution R A) 4

lemma cellPathNonpositiveToCell_projection (A : Mon (Complex R)) :
    cellPathNonpositiveToCell R A ≫ cellAugmentation R A = cellPathNonpositiveProjection R A :=
  Category.assoc _ _ _

lemma cellPathNonpositiveComparison_toCell {A B : Mon (Complex R)} (f : A ⟶ B) :
    cellPathNonpositiveComparison R f = cellPathNonpositiveToCell R A ≫ cellResolutionMap R f :=
  (Category.assoc _ _ _).symm

def cellPathNonpositiveToDoubleCell (A : Mon (Complex R)) :
    cellPathNonpositiveSource R A ⟶ cellResolution R (cellResolution R A) :=
  connectiveCoverInclusion R (iteratedCellResolution R (cellResolution R A) 4) ≫
    iteratedCellAugmentation R (cellResolution R (cellResolution R A)) 3

lemma cellPathNonpositiveToDoubleCell_toCell (A : Mon (Complex R)) :
    cellPathNonpositiveToDoubleCell R A ≫ cellAugmentation R (cellResolution R A) =
      cellPathNonpositiveToCell R A := by
  simp only [cellPathNonpositiveToDoubleCell, cellPathNonpositiveToCell,
    iteratedCellAugmentation, iteratedCellResolution, Category.assoc, Category.comp_id]

lemma cellPathNonpositiveToDoubleCell_projection (A : Mon (Complex R)) :
    cellPathNonpositiveToDoubleCell R A ≫ iteratedCellAugmentation R A 2 =
      cellPathNonpositiveProjection R A := by
  simp only [iteratedCellAugmentation, iteratedCellResolution, Category.comp_id]
  rw [← Category.assoc, cellPathNonpositiveToDoubleCell_toCell,
    cellPathNonpositiveToCell_projection]

def Path.Witness.precompNonpositiveCell {A T : Mon (Complex R)}
    {f g : cellResolution R A ⟶ T}
    (w : Path.Witness R (cellAugmentation R (cellResolution R A) ≫ f)
      (cellAugmentation R (cellResolution R A) ≫ g)) :
    Path.Witness R (cellPathNonpositiveToCell R A ≫ f) (cellPathNonpositiveToCell R A ≫ g) where
  hom := cellPathNonpositiveToDoubleCell R A ≫ w.hom
  source_eq := by
    rw [Category.assoc, w.source_eq, ← Category.assoc, cellPathNonpositiveToDoubleCell_toCell]
  target_eq := by
    rw [Category.assoc, w.target_eq, ← Category.assoc, cellPathNonpositiveToDoubleCell_toCell]

def Path.Witness.precompNonpositiveDouble {A T : Mon (Complex R)} {f g : A ⟶ T}
    (w : Path.Witness R
      (cellAugmentation R (cellResolution R A) ≫ cellAugmentation R A ≫ f)
      (cellAugmentation R (cellResolution R A) ≫ cellAugmentation R A ≫ g)) :
    Path.Witness R (cellPathNonpositiveProjection R A ≫ f)
      (cellPathNonpositiveProjection R A ≫ g) where
  hom := cellPathNonpositiveToDoubleCell R A ≫ w.hom
  source_eq := by
    rw [Category.assoc, w.source_eq, ← Category.assoc, cellPathNonpositiveToDoubleCell_toCell,
      ← Category.assoc, cellPathNonpositiveToCell_projection]
  target_eq := by
    rw [Category.assoc, w.target_eq, ← Category.assoc, cellPathNonpositiveToDoubleCell_toCell,
      ← Category.assoc, cellPathNonpositiveToCell_projection]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
