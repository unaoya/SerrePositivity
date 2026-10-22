module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCellPathNaturality
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovClassNaturality

/-!
概要：指定底経路に沿う classifying map の自然性を、元の両端比較付き実二重経路で示す。
方針：摂動射上で四辺を固定して充填し、元の class 射を後合成する。
規約：任意の追加の二重経路は入力しない。使われ方：新 Γ の実右三角形。
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
  (n : ℤ) (hn : 0 ≤ n) {b₀ b₁ : P ⟶ postnikov R B n}
  (w : Path.Witness R b₀ b₁) (f : B ⟶ C)

def postnikovCellPathNaturalitySquare : Path.Witness R
    (cellAugmentation R (cellPathNonpositiveSource R P) ≫
      (postnikovCellPathNaturalityLeft R B C P n hn w f).hom)
    (cellAugmentation R (cellPathNonpositiveSource R P) ≫
      (postnikovCellPathNaturalityRight R B C P n hn w f).hom) :=
  cellBoundaryRectangleSquare R (postnikovPerturbedProjection R C n hn)
    (postnikovPerturbedProjection_surjective R C n hn)
    (postnikovPerturbedProjection_quasiIso R C n hn)
    (postnikovCellPathNaturalityLeft R B C P n hn w f)
    (postnikovCellPathNaturalityRight R B C P n hn w f)
    ((postnikovCellLiftOverNaturalityWitness R B C P n hn b₀ f).precompNonpositiveCell R)
    ((postnikovCellLiftOverNaturalityWitness R B C P n hn b₁ f).precompNonpositiveCell R)
    (postnikovCellPathNaturality_base_eq R B C P n hn w f)
    (postnikovCellPathNaturalityCorner_relative R B C P n hn f b₀)
    (postnikovCellPathNaturalityCorner_relative R B C P n hn f b₁)

lemma postnikovCellPathNaturalityLeft_class :
    (postnikovCellPathNaturalityLeft R B C P n hn w f).hom ≫
      Path.map R (postnikovPerturbedClass R C n hn) =
    ((cellPathNonpositiveFixedWitness R w).hom ≫ Path.map R (postnikovCellClass R B n hn)) ≫
      Path.map R (postnikovDerivationTargetMap R f n hn) := by
  change ((cellPathNonpositiveFixedWitness R w).hom ≫
    Path.map R (postnikovCellLift R B n hn ≫ postnikovPerturbedMap R f n hn)) ≫ _ = _
  rw [Category.assoc, ← Path.map_comp, Category.assoc, postnikovPerturbedClass_naturality,
    ← Category.assoc]
  change (cellPathNonpositiveFixedWitness R w).hom ≫
    Path.map R (postnikovCellClass R B n hn ≫ postnikovDerivationTargetMap R f n hn) = _
  rw [Path.map_comp, ← Category.assoc]

lemma postnikovCellPathNaturalityRight_class :
    (postnikovCellPathNaturalityRight R B C P n hn w f).hom ≫
      Path.map R (postnikovPerturbedClass R C n hn) =
    (cellPathNonpositiveFixedWitness R (w.postcomp (postnikovMap R f n))).hom ≫
      Path.map R (postnikovCellClass R C n hn) := by
  change ((cellPathNonpositiveFixedWitness R (w.postcomp (postnikovMap R f n))).hom ≫
    Path.map R (postnikovCellLift R C n hn)) ≫ _ = _
  rw [Category.assoc, ← Path.map_comp]
  rfl

def postnikovCellClassPathNaturalitySquare : Path.Witness R
    (cellAugmentation R (cellPathNonpositiveSource R P) ≫
      ((cellPathNonpositiveFixedWitness R w).hom ≫ Path.map R (postnikovCellClass R B n hn)) ≫
      Path.map R (postnikovDerivationTargetMap R f n hn))
    (cellAugmentation R (cellPathNonpositiveSource R P) ≫
      (cellPathNonpositiveFixedWitness R (w.postcomp (postnikovMap R f n))).hom ≫
      Path.map R (postnikovCellClass R C n hn)) where
  hom := (postnikovCellPathNaturalitySquare R B C P n hn w f).hom ≫
    Path.map R (Path.map R (postnikovPerturbedClass R C n hn))
  source_eq := by
    rw [Category.assoc, Path.map_source, ← Category.assoc,
      (postnikovCellPathNaturalitySquare R B C P n hn w f).source_eq, Category.assoc,
      postnikovCellPathNaturalityLeft_class]
  target_eq := by
    rw [Category.assoc, Path.map_target, ← Category.assoc,
      (postnikovCellPathNaturalitySquare R B C P n hn w f).target_eq, Category.assoc,
      postnikovCellPathNaturalityRight_class]

lemma postnikovCellClassPathNaturalitySquare_source_trace :
    (postnikovCellClassPathNaturalitySquare R B C P n hn w f).hom ≫
      Path.map R (Path.source R (postnikovDerivationTarget R C n hn)) =
    cellAugmentation R (cellPathNonpositiveSource R P) ≫
      ((postnikovCellClassOverNaturalityWitness R B C P n hn b₀ f).precompNonpositiveCell
        R).hom := by
  change ((postnikovCellPathNaturalitySquare R B C P n hn w f).hom ≫
    Path.map R (Path.map R (postnikovPerturbedClass R C n hn))) ≫ _ = _
  rw [Category.assoc, ← Path.map_comp, Path.map_source, Path.map_comp, ← Category.assoc]
  change ((cellBoundaryRectangleSquare R _ _ _ _ _ _ _ _ _ _).hom ≫ _) ≫ _ = _
  rw [cellBoundaryRectangleSquare_source_trace]
  rfl

lemma postnikovCellClassPathNaturalitySquare_target_trace :
    (postnikovCellClassPathNaturalitySquare R B C P n hn w f).hom ≫
      Path.map R (Path.target R (postnikovDerivationTarget R C n hn)) =
    cellAugmentation R (cellPathNonpositiveSource R P) ≫
      ((postnikovCellClassOverNaturalityWitness R B C P n hn b₁ f).precompNonpositiveCell
        R).hom := by
  change ((postnikovCellPathNaturalitySquare R B C P n hn w f).hom ≫
    Path.map R (Path.map R (postnikovPerturbedClass R C n hn))) ≫ _ = _
  rw [Category.assoc, ← Path.map_comp, Path.map_target, Path.map_comp, ← Category.assoc]
  change ((cellBoundaryRectangleSquare R _ _ _ _ _ _ _ _ _ _).hom ≫ _) ≫ _ = _
  rw [cellBoundaryRectangleSquare_target_trace]
  rfl

lemma postnikovCellClassPathNaturalitySquare_base_trace :
    (postnikovCellClassPathNaturalitySquare R B C P n hn w f).hom ≫
      Path.map R (Path.map R (SquareZero.projection (postnikov R C n)
        (postnikovShiftedLayerBimodule R C n hn 1))) =
    cellAugmentation R (cellPathNonpositiveSource R P) ≫
      ((cellPathNonpositiveProjection R P ≫ (w.postcomp (postnikovMap R f n)).hom) ≫
        Path.diagonal R (Path.algebra R (postnikov R C n))) := by
  change ((postnikovCellPathNaturalitySquare R B C P n hn w f).hom ≫
    Path.map R (Path.map R (postnikovPerturbedClass R C n hn))) ≫ _ = _
  rw [Category.assoc, ← Path.map_comp, ← Path.map_comp, postnikovPerturbedClass_projection]
  change (cellBoundaryRectangleSquare R _ _ _ _ _ _ _ _ _ _).hom ≫ _ = _
  rw [cellBoundaryRectangleSquare_base_trace, postnikovCellPathNaturalityLeft_base]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
