module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCellLiftOverNaturality
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCellClassOver
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroBaseChangeWitness

/-!
概要：任意の底射で引き戻した元の class の自然性を、共通底上の実相対経路にする。
方針：実 cell lift の経路へ class を後合成し、定数底の平方零経路を持ち上げる。
規約：二重 cell augmentation と元の係数を保持。使われ方：roof の右 class 像の比較。
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

abbrev postnikovCellClassOverForward := cellResolutionMap R b ≫
  postnikovCellClass R B n hn ≫ postnikovDerivationTargetMap R f n hn

abbrev postnikovCellClassOverComposite := cellResolutionMap R (b ≫ postnikovMap R f n) ≫
  postnikovCellClass R C n hn

lemma postnikovCellClassOverForward_projection : postnikovCellClassOverForward R B C P n hn b f ≫
    SquareZero.projection (postnikov R C n) (postnikovShiftedLayerBimodule R C n hn 1) =
      cellAugmentation R P ≫ b ≫ postnikovMap R f n := by
  simp only [postnikovCellClassOverForward, Category.assoc]
  rw [postnikovDerivationTargetMap_projection,
    reassoc_of% (postnikovCellClass_projection R B n hn),
    reassoc_of% (cellResolutionMap_augmentation R b)]

lemma postnikovCellClassOverComposite_projection :
    postnikovCellClassOverComposite R B C P n hn b f ≫
      SquareZero.projection (postnikov R C n) (postnikovShiftedLayerBimodule R C n hn 1) =
        cellAugmentation R P ≫ b ≫ postnikovMap R f n := by
  rw [postnikovCellClassOverComposite, Category.assoc, postnikovCellClass_projection,
    cellResolutionMap_augmentation]

def postnikovCellClassOverNaturalityWitness : Path.Witness R
    (cellAugmentation R (cellResolution R P) ≫ postnikovCellClassOverForward R B C P n hn b f)
    (cellAugmentation R (cellResolution R P) ≫
      postnikovCellClassOverComposite R B C P n hn b f) where
  hom := ((postnikovCellLiftOverNaturalityWitness R B C P n hn b f).postcomp
    (postnikovPerturbedClass R C n hn)).hom
  source_eq := by
    rw [((postnikovCellLiftOverNaturalityWitness R B C P n hn b f).postcomp
      (postnikovPerturbedClass R C n hn)).source_eq]
    simp only [postnikovCellLiftOverSource, postnikovCellClassOverForward, Category.assoc,
      postnikovPerturbedClass_naturality, postnikovCellClass]
  target_eq := by
    rw [((postnikovCellLiftOverNaturalityWitness R B C P n hn b f).postcomp
      (postnikovPerturbedClass R C n hn)).target_eq]
    simp only [postnikovCellLiftOverTarget, postnikovCellClassOverComposite, postnikovCellClass,
      Category.assoc]

lemma postnikovCellClassOverNaturalityWitness_relative :
    (postnikovCellClassOverNaturalityWitness R B C P n hn b f).hom ≫
      Path.map R (SquareZero.projection (postnikov R C n)
        (postnikovShiftedLayerBimodule R C n hn 1)) =
    (cellAugmentation R (cellResolution R P) ≫ cellAugmentation R P ≫ b ≫ postnikovMap R f n) ≫
      Path.diagonal R (postnikov R C n) := by
  change ((postnikovCellLiftOverNaturalityWitness R B C P n hn b f).hom ≫
    Path.map R (postnikovPerturbedClass R C n hn)) ≫ Path.map R _ = _
  rw [Category.assoc, ← Path.map_comp, postnikovPerturbedClass_projection,
    postnikovCellLiftOverNaturalityWitness_relative]

lemma postnikovCellClassOverForward_base :
    (cellAugmentation R (cellResolution R P) ≫ postnikovCellClassOverForward R B C P n hn b f) ≫
      SquareZero.projection (postnikov R C n) (postnikovShiftedLayerBimodule R C n hn 1) =
    (cellAugmentation R (cellResolution R P) ≫ cellAugmentation R P) ≫
      (b ≫ postnikovMap R f n) := by
  rw [Category.assoc, postnikovCellClassOverForward_projection, Category.assoc]

lemma postnikovCellClassOverComposite_base :
    (cellAugmentation R (cellResolution R P) ≫ postnikovCellClassOverComposite R B C P n hn b f) ≫
      SquareZero.projection (postnikov R C n) (postnikovShiftedLayerBimodule R C n hn 1) =
    (cellAugmentation R (cellResolution R P) ≫ cellAugmentation R P) ≫
      (b ≫ postnikovMap R f n) := by
  rw [Category.assoc, postnikovCellClassOverComposite_projection, Category.assoc]

def postnikovCellClassOverNaturalitySource := SquareZero.baseChangeLift (b ≫ postnikovMap R f n)
  (postnikovShiftedLayerBimodule R C n hn 1)
  (cellAugmentation R (cellResolution R P) ≫ cellAugmentation R P)
  (cellAugmentation R (cellResolution R P) ≫ postnikovCellClassOverForward R B C P n hn b f)
  (postnikovCellClassOverForward_base R B C P n hn b f)

def postnikovCellClassOverNaturalityTarget := SquareZero.baseChangeLift (b ≫ postnikovMap R f n)
  (postnikovShiftedLayerBimodule R C n hn 1)
  (cellAugmentation R (cellResolution R P) ≫ cellAugmentation R P)
  (cellAugmentation R (cellResolution R P) ≫ postnikovCellClassOverComposite R B C P n hn b f)
  (postnikovCellClassOverComposite_base R B C P n hn b f)

def postnikovCellClassOverRelativeWitness : Path.Witness R
    (postnikovCellClassOverNaturalitySource R B C P n hn b f)
    (postnikovCellClassOverNaturalityTarget R B C P n hn b f) :=
  SquareZero.baseChangeWitness _ _ _ _ _ _ _
    (postnikovCellClassOverNaturalityWitness R B C P n hn b f)
    (by simpa only [Category.assoc] using
      postnikovCellClassOverNaturalityWitness_relative R B C P n hn b f)

lemma postnikovCellClassOverRelativeWitness_projection :
    (postnikovCellClassOverRelativeWitness R B C P n hn b f).hom ≫
      Path.map R (SquareZero.projection P
        (bimoduleRestrict (b ≫ postnikovMap R f n) (postnikovShiftedLayerBimodule R C n hn 1))) =
    (cellAugmentation R (cellResolution R P) ≫ cellAugmentation R P) ≫ Path.diagonal R P :=
  SquareZero.baseChangeWitness_relative _ _ _ _ _ _ _ _ _

lemma postnikovCellClassOverNaturalityTarget_eq :
    postnikovCellClassOverNaturalityTarget R B C P n hn b f =
      cellAugmentation R (cellResolution R P) ≫
        postnikovCellClassOver R C P n hn (b ≫ postnikovMap R f n) := by
  apply SquareZero.baseChange_hom_ext (b ≫ postnikovMap R f n)
    (postnikovShiftedLayerBimodule R C n hn 1)
  · rw [postnikovCellClassOverNaturalityTarget, SquareZero.baseChangeLift_projection,
      Category.assoc, postnikovCellClassOver_projection]
  · rw [postnikovCellClassOverNaturalityTarget, SquareZero.baseChangeLift_map,
      Category.assoc, postnikovCellClassOver_map]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
