module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraCellComparisonComposition
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCellDerivation

/-!
概要：底射の合成に沿う二つの cell class 比較を、元の底に相対的な経路で結ぶ。
方針：cell 比較の合成経路へ元の class を後合成し、射影を augmentation で照合する。
規約：二重 cell 源と底の定数経路を保持。使われ方：roof 上の class の自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (B P Q : Mon (Complex R)) [B.X.IsStrictlyLE 0]
  (n : ℤ) (hn : 0 ≤ n) (a : P ⟶ Q) (b : Q ⟶ postnikov R B n)

def postnikovCellClassCompositionWitness : Path.Witness R
    ((cellAugmentation R (cellResolution R P) ≫
      (cellResolutionMap R a ≫ cellResolutionMap R b)) ≫ postnikovCellClass R B n hn)
    ((cellAugmentation R (cellResolution R P) ≫ cellResolutionMap R (a ≫ b)) ≫
      postnikovCellClass R B n hn) :=
  (cellResolutionMapCompositionWitness R a b).postcomp (postnikovCellClass R B n hn)

lemma postnikovCellClassCompositionWitness_relative :
    (postnikovCellClassCompositionWitness R B P Q n hn a b).hom ≫
      Path.map R (SquareZero.projection (postnikov R B n)
        (postnikovShiftedLayerBimodule R B n hn 1)) =
    (cellAugmentation R (cellResolution R P) ≫ cellAugmentation R P ≫ a ≫ b) ≫
      Path.diagonal R (postnikov R B n) := by
  change ((cellResolutionMapCompositionWitness R a b).hom ≫
    Path.map R (postnikovCellClass R B n hn)) ≫ Path.map R _ = _
  rw [Category.assoc, ← Path.map_comp, postnikovCellClass_projection,
    cellResolutionMapCompositionWitness_relative]
  simp only [Category.assoc, cellResolutionMap_augmentation]
  rw [reassoc_of% (cellResolutionMap_augmentation R a)]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
