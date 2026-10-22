module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCellClassOverNaturality
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRestrictionCoefficient

/-!
概要：共通底上の class 自然性経路の始点を、元の class の実係数像と同定する。
方針：制限した層射の平方零射と底変更の可換式で、元の二つの射影を照合する。
規約：元の係数像と二重 cell augmentation を保持。使われ方：roof の右 class 像。
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

def postnikovCellClassOverCoefficient :
    bimoduleRestrict b (postnikovShiftedLayerBimodule R B n hn 1) ⟶
      bimoduleRestrict (b ≫ postnikovMap R f n) (postnikovShiftedLayerBimodule R C n hn 1) :=
  bimoduleRestrictOver b (b ≫ postnikovMap R f n) (postnikovMap R f n) rfl
    (postnikovShiftedLayerMap R B n hn 1 f)

lemma postnikovCellClassOverCoefficient_hom :
    (postnikovCellClassOverCoefficient R B C P n hn b f).hom =
      (postnikovLayerMap R f n)⟦(1 : ℤ)⟧' :=
  (bimoduleRestrictOver_hom b (b ≫ postnikovMap R f n) (postnikovMap R f n) rfl
    (postnikovShiftedLayerMap R B n hn 1 f)).trans (postnikovShiftedLayerMap_hom R B n hn 1 f)

lemma postnikovCellClassOverNaturalitySource_eq :
    postnikovCellClassOverNaturalitySource R B C P n hn b f =
      cellAugmentation R (cellResolution R P) ≫ postnikovCellClassOver R B P n hn b ≫
        SquareZero.coefficientMap P (postnikovCellClassOverCoefficient R B C P n hn b f) := by
  apply SquareZero.baseChange_hom_ext (b ≫ postnikovMap R f n)
    (postnikovShiftedLayerBimodule R C n hn 1)
  · rw [postnikovCellClassOverNaturalitySource, SquareZero.baseChangeLift_projection,
      Category.assoc, Category.assoc, SquareZero.coefficientMap_projection,
      postnikovCellClassOver_projection]
  · rw [postnikovCellClassOverNaturalitySource, SquareZero.baseChangeLift_map]
    simp only [Category.assoc, postnikovCellClassOverCoefficient]
    rw [SquareZero.restrictionCoefficient_baseChange,
      ← Category.assoc (postnikovCellClassOver R B P n hn b), postnikovCellClassOver_map]
    simp only [postnikovCellClassOverForward, postnikovDerivationTargetMap, Category.assoc]

/-- 元の class の係数像と、元の合成底で引き戻した class の間の実相対経路。 -/
def postnikovCellClassOverImageWitness : Path.Witness R
    (cellAugmentation R (cellResolution R P) ≫ postnikovCellClassOver R B P n hn b ≫
      SquareZero.coefficientMap P (postnikovCellClassOverCoefficient R B C P n hn b f))
    (cellAugmentation R (cellResolution R P) ≫
      postnikovCellClassOver R C P n hn (b ≫ postnikovMap R f n)) where
  hom := (postnikovCellClassOverRelativeWitness R B C P n hn b f).hom
  source_eq := (postnikovCellClassOverRelativeWitness R B C P n hn b f).source_eq.trans
    (postnikovCellClassOverNaturalitySource_eq R B C P n hn b f)
  target_eq := (postnikovCellClassOverRelativeWitness R B C P n hn b f).target_eq.trans
    (postnikovCellClassOverNaturalityTarget_eq R B C P n hn b f)

lemma postnikovCellClassOverImageWitness_relative :
    (postnikovCellClassOverImageWitness R B C P n hn b f).hom ≫
      Path.map R (SquareZero.projection P
        (bimoduleRestrict (b ≫ postnikovMap R f n) (postnikovShiftedLayerBimodule R C n hn 1))) =
    (cellAugmentation R (cellResolution R P) ≫ cellAugmentation R P) ≫ Path.diagonal R P :=
  postnikovCellClassOverRelativeWitness_projection R B C P n hn b f

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
