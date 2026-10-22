module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCellDerivation
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraCellResolutionMap
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroBaseChangeLift
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroCoefficientFormula

/-!
概要：元の Postnikov cell class を任意の指定底射に沿って同じ底へ引き戻す。
方針：cell 比較と augmentation の厳密な式を使い、平方零の底変更を構成する。
規約：比較射の関手則や class 整合の経路は仮定しない。使われ方：roof 上の二つの class。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (B P : Mon (Complex R)) [B.X.IsStrictlyLE 0]
  (n : ℤ) (hn : 0 ≤ n) (b : P ⟶ postnikov R B n)

lemma postnikovCellClassOver_square : (cellResolutionMap R b ≫ postnikovCellClass R B n hn) ≫
    SquareZero.projection (postnikov R B n) (postnikovShiftedLayerBimodule R B n hn 1) =
      cellAugmentation R P ≫ b := by
  rw [Category.assoc, postnikovCellClass_projection, cellResolutionMap_augmentation]

def postnikovCellClassOver : cellResolution R P ⟶
    SquareZero.algebra P (bimoduleRestrict b (postnikovShiftedLayerBimodule R B n hn 1)) :=
  SquareZero.baseChangeLift b _ (cellAugmentation R P)
    (cellResolutionMap R b ≫ postnikovCellClass R B n hn)
    (postnikovCellClassOver_square R B P n hn b)

lemma postnikovCellClassOver_projection : postnikovCellClassOver R B P n hn b ≫
    SquareZero.projection P (bimoduleRestrict b (postnikovShiftedLayerBimodule R B n hn 1)) =
      cellAugmentation R P := SquareZero.baseChangeLift_projection _ _ _ _ _

lemma postnikovCellClassOver_map : postnikovCellClassOver R B P n hn b ≫
    SquareZero.baseChangeMap b (postnikovShiftedLayerBimodule R B n hn 1) =
      cellResolutionMap R b ≫ postnikovCellClass R B n hn :=
  SquareZero.baseChangeLift_map _ _ _ _ _

lemma postnikovCellClassOver_coefficient : (postnikovCellClassOver R B P n hn b).hom ≫
    (biprod.snd : P.X ⊞ (postnikovShiftedLayerBimodule R B n hn 1).X ⟶ _) =
      (cellResolutionMap R b).hom ≫ (postnikovCellDerivation R B n hn).hom := by
  rw [postnikovCellClassOver, SquareZero.baseChangeLift_hom, biprod.lift_snd]
  rfl

lemma postnikovCellClassOver_map_coefficient {N : Bimod P P}
    (u : bimoduleRestrict b (postnikovShiftedLayerBimodule R B n hn 1) ⟶ N) :
    (postnikovCellClassOver R B P n hn b ≫ SquareZero.coefficientMap P u).hom ≫
      (biprod.snd : P.X ⊞ N.X ⟶ N.X) =
        (cellResolutionMap R b).hom ≫ (postnikovCellDerivation R B n hn).hom ≫ u.hom := by
  let t : (postnikovShiftedLayerBimodule R B n hn 1).X ⟶ N.X := u.hom
  change (postnikovCellClassOver R B P n hn b).hom ≫
    biprod.map (𝟙 P.X) t ≫ (biprod.snd : P.X ⊞ N.X ⟶ N.X) =
      (cellResolutionMap R b).hom ≫ (postnikovCellDerivation R B n hn).hom ≫ t
  rw [biprod.map_snd, ← Category.assoc]
  exact (congrArg (fun x => x ≫ t) (postnikovCellClassOver_coefficient R B P n hn b)).trans
    (Category.assoc _ _ _)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
