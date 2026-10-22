module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraCellFixedPathNaturality
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraCellPathNonpositiveFixed

/-!
概要：cell 経路反映と後合成の自然性正方形を、既存の非正次数共通源へ移す。
方針：三重 cell 源への射を既存の五重 cell 源から作り、四辺と全底経路を計算する。
規約：既存の非正次数経路の射そのものを両端に保持。使われ方：指定右経路の自然性。
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

def cellFixedNonpositiveToTripleCell (A : Mon (Complex R)) : cellPathNonpositiveSource R A ⟶
    cellResolution R (cellResolution R (cellResolution R A)) :=
  connectiveCoverInclusion R _ ≫
    iteratedCellAugmentation R (cellResolution R (cellResolution R (cellResolution R A))) 2

lemma cellFixedNonpositiveToTripleCell_toDouble (A : Mon (Complex R)) :
    cellFixedNonpositiveToTripleCell R A ≫
      cellAugmentation R (cellResolution R (cellResolution R A)) =
    cellFixedNonpositiveToDoubleCell R A := by
  simp only [cellFixedNonpositiveToTripleCell, cellFixedNonpositiveToDoubleCell,
    iteratedCellAugmentation, iteratedCellResolution, Category.assoc, Category.comp_id]

lemma cellFixedNonpositiveToDoubleCell_projection (A : Mon (Complex R)) :
    cellFixedNonpositiveToDoubleCell R A ≫
      (cellAugmentation R (cellResolution R A) ≫ cellAugmentation R A) =
    cellPathNonpositiveProjection R A := by
  rw [← Category.assoc, cellFixedNonpositiveToDoubleCell_toCell]
  rfl

variable {A B C : Mon (Complex R)} {f g : A ⟶ B} (w : Path.Witness R f g) (u : B ⟶ C)

def cellFixedNonpositiveNaturalitySquare : Path.Witness R
    (((cellPathNonpositiveFixedWitness R w).postcomp (cellResolutionMap R u)).hom)
    ((cellPathNonpositiveFixedWitness R (w.postcomp u)).hom) where
  hom := cellFixedNonpositiveToTripleCell R A ≫ (cellFixedPathNaturalitySquare R w u).hom
  source_eq := by
    rw [Category.assoc, (cellFixedPathNaturalitySquare R w u).source_eq,
      ← Category.assoc, cellFixedNonpositiveToTripleCell_toDouble]
    change cellFixedNonpositiveToDoubleCell R A ≫
      ((cellResolutionMapFixedPathWitness R w).hom ≫ Path.map R (cellResolutionMap R u)) =
      (cellFixedNonpositiveToDoubleCell R A ≫ (cellResolutionMapFixedPathWitness R w).hom) ≫ _
    exact (Category.assoc _ _ _).symm
  target_eq := by
    rw [Category.assoc, (cellFixedPathNaturalitySquare R w u).target_eq,
      ← Category.assoc, cellFixedNonpositiveToTripleCell_toDouble]
    rfl

lemma cellFixedNonpositiveNaturalitySquare_source_trace :
    (cellFixedNonpositiveNaturalitySquare R w u).hom ≫
      Path.map R (Path.source R (cellResolution R C)) =
    cellFixedNonpositiveToDoubleCell R A ≫ (cellResolutionMapCompositionWitness R f u).hom := by
  change (cellFixedNonpositiveToTripleCell R A ≫ (cellFixedPathNaturalitySquare R w u).hom) ≫ _ = _
  rw [Category.assoc, cellFixedPathNaturalitySquare_source_trace, ← Category.assoc,
    cellFixedNonpositiveToTripleCell_toDouble]

lemma cellFixedNonpositiveNaturalitySquare_target_trace :
    (cellFixedNonpositiveNaturalitySquare R w u).hom ≫
      Path.map R (Path.target R (cellResolution R C)) =
    cellFixedNonpositiveToDoubleCell R A ≫ (cellResolutionMapCompositionWitness R g u).hom := by
  change (cellFixedNonpositiveToTripleCell R A ≫ (cellFixedPathNaturalitySquare R w u).hom) ≫ _ = _
  rw [Category.assoc, cellFixedPathNaturalitySquare_target_trace, ← Category.assoc,
    cellFixedNonpositiveToTripleCell_toDouble]

lemma cellFixedNonpositiveNaturalitySquare_base_trace :
    (cellFixedNonpositiveNaturalitySquare R w u).hom ≫
      Path.map R (Path.map R (cellAugmentation R C)) =
    (cellPathNonpositiveProjection R A ≫ (w.postcomp u).hom) ≫
      Path.diagonal R (Path.algebra R C) := by
  change (cellFixedNonpositiveToTripleCell R A ≫ (cellFixedPathNaturalitySquare R w u).hom) ≫ _ = _
  rw [Category.assoc, cellFixedPathNaturalitySquare_base_trace, ← Category.assoc,
    cellFixedNonpositiveToTripleCell_toDouble]
  rw [← Category.assoc (cellFixedNonpositiveToDoubleCell R A),
    ← Category.assoc (cellFixedNonpositiveToDoubleCell R A),
    cellFixedNonpositiveToDoubleCell_projection]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
