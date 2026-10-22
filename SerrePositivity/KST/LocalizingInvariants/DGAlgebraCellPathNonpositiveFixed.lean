module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraCellComparisonFixedPath
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraCellPathNonpositive

/-!
概要：既存の非正次数共通源と比較射の両端を保ち、底の全経路も固定する。
方針：二重 cell 源の境界持ち上げを、既存の五重 cell 源と connective cover へ移す。
規約：旧 cell 経路との一致は仮定しない。使われ方：元の右経路を保つ代替 class 比較。
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

def cellFixedNonpositiveToDoubleCell (A : Mon (Complex R)) : cellPathNonpositiveSource R A ⟶
    cellResolution R (cellResolution R A) :=
  connectiveCoverInclusion R _ ≫
    iteratedCellAugmentation R (cellResolution R (cellResolution R A)) 3

lemma cellFixedNonpositiveToDoubleCell_toCell (A : Mon (Complex R)) :
    cellFixedNonpositiveToDoubleCell R A ≫ cellAugmentation R (cellResolution R A) =
      connectiveCoverInclusion R _ ≫ iteratedCellAugmentation R (cellResolution R A) 4 := by
  simp only [cellFixedNonpositiveToDoubleCell, iteratedCellAugmentation, iteratedCellResolution,
    Category.assoc, Category.comp_id]

variable {A B : Mon (Complex R)} {f g : A ⟶ B} (w : Path.Witness R f g)

def cellPathNonpositiveFixedWitness : Path.Witness R (cellPathNonpositiveComparison R f)
    (cellPathNonpositiveComparison R g) where
  hom := cellFixedNonpositiveToDoubleCell R A ≫ (cellResolutionMapFixedPathWitness R w).hom
  source_eq := by
    rw [Category.assoc, (cellResolutionMapFixedPathWitness R w).source_eq,
      ← Category.assoc, cellFixedNonpositiveToDoubleCell_toCell]
    rfl
  target_eq := by
    rw [Category.assoc, (cellResolutionMapFixedPathWitness R w).target_eq,
      ← Category.assoc, cellFixedNonpositiveToDoubleCell_toCell]
    rfl

lemma cellPathNonpositiveFixedWitness_map : (cellPathNonpositiveFixedWitness R w).hom ≫
    Path.map R (cellAugmentation R B) = cellPathNonpositiveProjection R A ≫ w.hom := by
  change (cellFixedNonpositiveToDoubleCell R A ≫
    (cellResolutionMapFixedPathWitness R w).hom) ≫ _ = _
  rw [Category.assoc, cellResolutionMapFixedPathWitness_map,
    ← Category.assoc (cellFixedNonpositiveToDoubleCell R A),
    ← Category.assoc (cellFixedNonpositiveToDoubleCell R A)
      (cellAugmentation R (cellResolution R A)) (cellAugmentation R A),
    cellFixedNonpositiveToDoubleCell_toCell]
  simp only [cellPathNonpositiveProjection, Category.assoc]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
