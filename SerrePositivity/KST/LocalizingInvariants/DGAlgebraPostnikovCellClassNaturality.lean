module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCellLiftNaturality

/-!
概要：元の選択した cell class は、元の二つの比較射に沿って相対経路で自然である。
方針：cell lift の実相対経路に負符号の class を後合成し、両端を厳密な自然性で照合。
規約：二重 cell augmentation の前合成を明記。使われ方：LT の導来 class の像制限。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] {B C : Mon (Complex R)}
  [B.X.IsStrictlyLE 0] [C.X.IsStrictlyLE 0] (f : B ⟶ C) (n : ℤ) (hn : 0 ≤ n)

def postnikovCellClassNaturalityWitness : Path.Witness R
    (cellAugmentation R (cellResolution R (postnikov R B n)) ≫
      postnikovCellClass R B n hn ≫ postnikovDerivationTargetMap R f n hn)
    (cellAugmentation R (cellResolution R (postnikov R B n)) ≫
      cellResolutionMap R (postnikovMap R f n) ≫ postnikovCellClass R C n hn) where
  hom := ((postnikovCellLiftNaturalityWitness R f n hn).postcomp
    (postnikovPerturbedClass R C n hn)).hom
  source_eq := by
    rw [((postnikovCellLiftNaturalityWitness R f n hn).postcomp
      (postnikovPerturbedClass R C n hn)).source_eq]
    simp only [Category.assoc, postnikovPerturbedClass_naturality, postnikovCellClass]
  target_eq := by
    rw [((postnikovCellLiftNaturalityWitness R f n hn).postcomp
      (postnikovPerturbedClass R C n hn)).target_eq]
    simp only [Category.assoc, postnikovCellClass]

lemma postnikovCellClassNaturalityWitness_relative :
    (postnikovCellClassNaturalityWitness R f n hn).hom ≫
      Path.map R (SquareZero.projection (postnikov R C n)
        (postnikovShiftedLayerBimodule R C n hn 1)) =
        (cellAugmentation R (cellResolution R (postnikov R B n)) ≫
          cellAugmentation R (postnikov R B n) ≫ postnikovMap R f n) ≫
            Path.diagonal R (postnikov R C n) := by
  change ((postnikovCellLiftNaturalityWitness R f n hn).hom ≫
    Path.map R (postnikovPerturbedClass R C n hn)) ≫ Path.map R _ = _
  rw [Category.assoc, ← Path.map_comp, postnikovPerturbedClass_projection,
    postnikovCellLiftNaturalityWitness_relative]
  rw [Category.assoc (postnikovCellLift R B n hn),
    postnikovPerturbedProjection_naturality, ← Category.assoc (postnikovCellLift R B n hn),
    postnikovCellLift_projection]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
