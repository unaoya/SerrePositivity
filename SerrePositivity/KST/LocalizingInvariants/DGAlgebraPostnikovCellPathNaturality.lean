module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraCellFixedNonpositiveNaturality
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCellOverClassComparison
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraCellPathSourceMap

/-!
概要：実 Postnikov 摂動 lift の自然性を、任意の指定底経路の両端にそろえる。
方針：底経路の cell 反映を摂動代数へ送り、両端の既存の自然性経路を保持する。
規約：底の全経路を元の w の像に固定。使われ方：classifying map の右三角形。
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

def postnikovCellPathNaturalityLeft : Path.Witness R
    (cellPathNonpositiveToCell R P ≫ postnikovCellLiftOverSource R B C P n hn b₀ f)
    (cellPathNonpositiveToCell R P ≫ postnikovCellLiftOverSource R B C P n hn b₁ f) where
  hom := (cellPathNonpositiveFixedWitness R w).hom ≫
    Path.map R (postnikovCellLift R B n hn ≫ postnikovPerturbedMap R f n hn)
  source_eq := by
    rw [Category.assoc, Path.map_source, ← Category.assoc,
      (cellPathNonpositiveFixedWitness R w).source_eq]
    simp only [cellPathNonpositiveComparison_toCell, postnikovCellLiftOverSource, Category.assoc]
  target_eq := by
    rw [Category.assoc, Path.map_target, ← Category.assoc,
      (cellPathNonpositiveFixedWitness R w).target_eq]
    simp only [cellPathNonpositiveComparison_toCell, postnikovCellLiftOverSource, Category.assoc]

def postnikovCellPathNaturalityRight : Path.Witness R
    (cellPathNonpositiveToCell R P ≫ postnikovCellLiftOverTarget R B C P n hn b₀ f)
    (cellPathNonpositiveToCell R P ≫ postnikovCellLiftOverTarget R B C P n hn b₁ f) where
  hom := (cellPathNonpositiveFixedWitness R (w.postcomp (postnikovMap R f n))).hom ≫
    Path.map R (postnikovCellLift R C n hn)
  source_eq := by
    rw [Category.assoc, Path.map_source, ← Category.assoc,
      (cellPathNonpositiveFixedWitness R (w.postcomp (postnikovMap R f n))).source_eq]
    simp only [cellPathNonpositiveComparison_toCell, postnikovCellLiftOverTarget, Category.assoc]
  target_eq := by
    rw [Category.assoc, Path.map_target, ← Category.assoc,
      (cellPathNonpositiveFixedWitness R (w.postcomp (postnikovMap R f n))).target_eq]
    simp only [cellPathNonpositiveComparison_toCell, postnikovCellLiftOverTarget, Category.assoc]

lemma postnikovCellPathNaturalityLeft_base :
    (postnikovCellPathNaturalityLeft R B C P n hn w f).hom ≫
      Path.map R (postnikovPerturbedProjection R C n hn) =
    cellPathNonpositiveProjection R P ≫ (w.postcomp (postnikovMap R f n)).hom := by
  change ((cellPathNonpositiveFixedWitness R w).hom ≫
    Path.map R (postnikovCellLift R B n hn ≫ postnikovPerturbedMap R f n hn)) ≫ _ = _
  rw [Category.assoc, ← Path.map_comp, Category.assoc,
    postnikovPerturbedProjection_naturality, ← Category.assoc, postnikovCellLift_projection,
    Path.map_comp, ← Category.assoc, cellPathNonpositiveFixedWitness_map]
  exact Category.assoc _ _ _

lemma postnikovCellPathNaturalityRight_base :
    (postnikovCellPathNaturalityRight R B C P n hn w f).hom ≫
      Path.map R (postnikovPerturbedProjection R C n hn) =
    cellPathNonpositiveProjection R P ≫ (w.postcomp (postnikovMap R f n)).hom := by
  change ((cellPathNonpositiveFixedWitness R (w.postcomp (postnikovMap R f n))).hom ≫
    Path.map R (postnikovCellLift R C n hn)) ≫ _ = _
  rw [Category.assoc, ← Path.map_comp, postnikovCellLift_projection,
    cellPathNonpositiveFixedWitness_map]

lemma postnikovCellPathNaturality_base_eq :
    (postnikovCellPathNaturalityLeft R B C P n hn w f).hom ≫
      Path.map R (postnikovPerturbedProjection R C n hn) =
    (postnikovCellPathNaturalityRight R B C P n hn w f).hom ≫
      Path.map R (postnikovPerturbedProjection R C n hn) := by
  rw [postnikovCellPathNaturalityLeft_base, postnikovCellPathNaturalityRight_base]

lemma postnikovCellPathNaturalityCorner_relative (b : P ⟶ postnikov R B n) :
    ((postnikovCellLiftOverNaturalityWitness R B C P n hn b f).precompNonpositiveCell R).hom ≫
      Path.map R (postnikovPerturbedProjection R C n hn) =
    ((cellPathNonpositiveToCell R P ≫ postnikovCellLiftOverSource R B C P n hn b f) ≫
      postnikovPerturbedProjection R C n hn) ≫ Path.diagonal R (postnikov R C n) := by
  have he := congrArg (fun t => cellPathNonpositiveToDoubleCell R P ≫ t)
    (postnikovCellOverNaturality_relative R B C P n hn b f)
  change (cellPathNonpositiveToDoubleCell R P ≫
    (postnikovCellLiftOverNaturalityWitness R B C P n hn b f).hom) ≫ _ = _
  rw [← cellPathNonpositiveToDoubleCell_toCell R P]
  simpa only [Category.assoc] using he

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
