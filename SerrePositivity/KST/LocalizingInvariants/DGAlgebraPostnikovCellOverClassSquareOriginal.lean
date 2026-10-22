module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCellOverClassSquare

/-!
概要：二重比較の基準となる class 経路を、元の指定済み相対自然性経路に同定する。
方針：底変更経路の二射影を照合し、経路の一意性で全射の一致を得る。
規約：cell augmentation を一回前合成した元の経路そのもの。使われ方：Γ への接続。
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

lemma postnikovCellOverCommonNaturality_map :
    (postnikovCellOverCommonComparison R B C P n hn b f
      (postnikovCellLiftOverNaturalityWitness R B C P n hn b f)
      (postnikovCellOverNaturality_relative R B C P n hn b f)).hom ≫
      Path.map R (SquareZero.baseChangeMap (b ≫ postnikovMap R f n)
        (postnikovShiftedLayerBimodule R C n hn 1)) =
    cellAugmentation R (cellResolution R (cellResolution R P)) ≫
      (postnikovCellClassOverNaturalityWitness R B C P n hn b f).hom := by
  rw [postnikovCellOverCommonComparison, SquareZero.baseChangeRelativeWitness_map]
  rfl

lemma postnikovCellOverCommonNaturality_hom :
    (postnikovCellOverCommonComparison R B C P n hn b f
      (postnikovCellLiftOverNaturalityWitness R B C P n hn b f)
      (postnikovCellOverNaturality_relative R B C P n hn b f)).hom =
    cellAugmentation R (cellResolution R (cellResolution R P)) ≫
      (postnikovCellClassOverRelativeWitness R B C P n hn b f).hom := by
  apply SquareZero.baseChangePath_hom_ext (b ≫ postnikovMap R f n)
    (postnikovShiftedLayerBimodule R C n hn 1)
  · rw [(postnikovCellOverCommonComparison R B C P n hn b f
      (postnikovCellLiftOverNaturalityWitness R B C P n hn b f)
      (postnikovCellOverNaturality_relative R B C P n hn b f)).projection_eq,
      Category.assoc, postnikovCellClassOverRelativeWitness_projection]
    simp only [postnikovCellOverComparisonProjection, Category.assoc]
  · rw [postnikovCellOverCommonNaturality_map, Category.assoc]
    have hm : (postnikovCellClassOverRelativeWitness R B C P n hn b f).hom ≫
        Path.map R (SquareZero.baseChangeMap (b ≫ postnikovMap R f n)
          (postnikovShiftedLayerBimodule R C n hn 1)) =
        (postnikovCellClassOverNaturalityWitness R B C P n hn b f).hom := by
      unfold postnikovCellClassOverRelativeWitness
      apply SquareZero.baseChangeWitness_map
    rw [hm]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
