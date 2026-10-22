module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraCellPathBoundaryRectangle
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraCellComparisonFixedPath
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraCellComparisonComposition

/-!
概要：指定底経路を保つ cell 反映と、元の代数射の後合成を実二重経路で比較する。
方針：両端の cell 合成比較を境界に使い、全底経路の厳密一致で長方形を充填する。
規約：元の w と u だけを入力する。使われ方：右経路の B 遷移との自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] {A B C : Mon (Complex R)} {f g : A ⟶ B}
  (w : Path.Witness R f g) (u : B ⟶ C)

def cellFixedPathPostWitness : Path.Witness R
    (cellAugmentation R (cellResolution R A) ≫ (cellResolutionMap R f ≫ cellResolutionMap R u))
    (cellAugmentation R (cellResolution R A) ≫
      (cellResolutionMap R g ≫ cellResolutionMap R u)) where
  hom := (cellResolutionMapFixedPathWitness R w).hom ≫ Path.map R (cellResolutionMap R u)
  source_eq := by
    rw [Category.assoc, Path.map_source, ← Category.assoc,
      (cellResolutionMapFixedPathWitness R w).source_eq, Category.assoc]
  target_eq := by
    rw [Category.assoc, Path.map_target, ← Category.assoc,
      (cellResolutionMapFixedPathWitness R w).target_eq, Category.assoc]

lemma cellFixedPathPostWitness_base : (cellFixedPathPostWitness R w u).hom ≫
    Path.map R (cellAugmentation R C) =
    (cellAugmentation R (cellResolution R A) ≫ cellAugmentation R A) ≫
      (w.postcomp u).hom := by
  change ((cellResolutionMapFixedPathWitness R w).hom ≫
    Path.map R (cellResolutionMap R u)) ≫ _ = _
  rw [Category.assoc, ← Path.map_comp, cellResolutionMap_augmentation,
    Path.map_comp, ← Category.assoc, cellResolutionMapFixedPathWitness_map]
  exact Category.assoc _ _ _

lemma cellFixedPathPostWitness_base_eq : (cellFixedPathPostWitness R w u).hom ≫
    Path.map R (cellAugmentation R C) =
    (cellResolutionMapFixedPathWitness R (w.postcomp u)).hom ≫
      Path.map R (cellAugmentation R C) := by
  rw [cellFixedPathPostWitness_base, cellResolutionMapFixedPathWitness_map]

lemma cellFixedPathNaturality_left_relative :
    (cellResolutionMapCompositionWitness R f u).hom ≫ Path.map R (cellAugmentation R C) =
    ((cellAugmentation R (cellResolution R A) ≫
      (cellResolutionMap R f ≫ cellResolutionMap R u)) ≫ cellAugmentation R C) ≫
      Path.diagonal R C := by
  simpa only [Category.assoc] using cellResolutionMapCompositionWitness_relative R f u

lemma cellFixedPathNaturality_right_relative :
    (cellResolutionMapCompositionWitness R g u).hom ≫ Path.map R (cellAugmentation R C) =
    ((cellAugmentation R (cellResolution R A) ≫
      (cellResolutionMap R g ≫ cellResolutionMap R u)) ≫ cellAugmentation R C) ≫
      Path.diagonal R C := by
  simpa only [Category.assoc] using cellResolutionMapCompositionWitness_relative R g u

def cellFixedPathNaturalitySquare : Path.Witness R
    (cellAugmentation R (cellResolution R (cellResolution R A)) ≫
      (cellFixedPathPostWitness R w u).hom)
    (cellAugmentation R (cellResolution R (cellResolution R A)) ≫
      (cellResolutionMapFixedPathWitness R (w.postcomp u)).hom) :=
  cellBoundaryRectangleSquare R (cellAugmentation R C) (cellAugmentation_surjective R C)
    (cellAugmentation_quasiIso R C) (cellFixedPathPostWitness R w u)
    (cellResolutionMapFixedPathWitness R (w.postcomp u))
    (cellResolutionMapCompositionWitness R f u) (cellResolutionMapCompositionWitness R g u)
    (cellFixedPathPostWitness_base_eq R w u) (cellFixedPathNaturality_left_relative R u)
    (cellFixedPathNaturality_right_relative R u)

lemma cellFixedPathNaturalitySquare_source_trace : (cellFixedPathNaturalitySquare R w u).hom ≫
    Path.map R (Path.source R (cellResolution R C)) =
      cellAugmentation R (cellResolution R (cellResolution R A)) ≫
        (cellResolutionMapCompositionWitness R f u).hom :=
  cellBoundaryRectangleSquare_source_trace R _ _ _ _ _ _ _ _ _ _

lemma cellFixedPathNaturalitySquare_target_trace : (cellFixedPathNaturalitySquare R w u).hom ≫
    Path.map R (Path.target R (cellResolution R C)) =
      cellAugmentation R (cellResolution R (cellResolution R A)) ≫
        (cellResolutionMapCompositionWitness R g u).hom :=
  cellBoundaryRectangleSquare_target_trace R _ _ _ _ _ _ _ _ _ _

lemma cellFixedPathNaturalitySquare_base_trace : (cellFixedPathNaturalitySquare R w u).hom ≫
    Path.map R (Path.map R (cellAugmentation R C)) =
    cellAugmentation R (cellResolution R (cellResolution R A)) ≫
      (((cellAugmentation R (cellResolution R A) ≫ cellAugmentation R A) ≫
        (w.postcomp u).hom) ≫ Path.diagonal R (Path.algebra R C)) := by
  change (cellBoundaryRectangleSquare R _ _ _ _ _ _ _ _ _ _).hom ≫ _ = _
  rw [cellBoundaryRectangleSquare_base_trace, cellFixedPathPostWitness_base]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
