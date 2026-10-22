module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCellImageRelative
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeWitnessMapOver

/-!
概要：元の第一自然性経路を第二係数射で写し、元の底変更 class 射と全経路で比較する。
方針：係数制限と平方零底変更の厳密な可換式を経路関手で写す。
規約：元の ImageWitness の全経路を保持。使われ方：affine 二段合成の第一辺の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (B C D P : Mon (Complex R))
  [B.X.IsStrictlyLE 0] [C.X.IsStrictlyLE 0] [D.X.IsStrictlyLE 0]
  (n : ℤ) (hn : 0 ≤ n) (b : P ⟶ postnikov R B n) (f : B ⟶ C) (g : C ⟶ D)

def postnikovCellImageForwardMap := SquareZero.coefficientMap P
  (postnikovCellClassOverCoefficient R C D P n hn (b ≫ postnikovMap R f n) g)

lemma postnikovCellImageForwardMap_projection :
    postnikovCellImageForwardMap R B C D P n hn b f g ≫ SquareZero.projection _ _ =
      SquareZero.projection _ _ ≫ 𝟙 P := by
  rw [Category.comp_id]
  exact SquareZero.coefficientMap_projection _ _

lemma postnikovCellImageForwardMap_map :
    postnikovCellImageForwardMap R B C D P n hn b f g ≫ SquareZero.baseChangeMap
      ((b ≫ postnikovMap R f n) ≫ postnikovMap R g n)
      (postnikovShiftedLayerBimodule R D n hn 1) =
    SquareZero.baseChangeMap (b ≫ postnikovMap R f n)
      (postnikovShiftedLayerBimodule R C n hn 1) ≫ postnikovDerivationTargetMap R g n hn :=
  SquareZero.restrictionCoefficient_baseChange _ _ _ _ _

def postnikovCellImageForwardRelative : SquareZero.RelativeWitness
    (cellAugmentation R (cellResolution R P) ≫ cellAugmentation R P)
    (bimoduleRestrict ((b ≫ postnikovMap R f n) ≫ postnikovMap R g n)
      (postnikovShiftedLayerBimodule R D n hn 1))
    ((cellAugmentation R (cellResolution R P) ≫ postnikovCellClassOver R B P n hn b ≫
      SquareZero.coefficientMap P (postnikovCellClassOverCoefficient R B C P n hn b f)) ≫
      postnikovCellImageForwardMap R B C D P n hn b f g)
    (cellAugmentation R (cellResolution R P) ≫
      postnikovCellClassOver R C P n hn (b ≫ postnikovMap R f n) ≫
        postnikovCellImageForwardMap R B C D P n hn b f g) := by
  let z := (postnikovCellImageRelative R B C P n hn b f).mapOver (𝟙 P)
    (postnikovCellImageForwardMap R B C D P n hn b f g)
    (postnikovCellImageForwardMap_projection R B C D P n hn b f g)
  refine {
    hom := z.hom
    source_eq := z.source_eq
    target_eq := z.target_eq.trans (Category.assoc _ _ _)
    projection_eq := ?_ }
  simpa only [Category.comp_id] using z.projection_eq

lemma postnikovCellImageForwardRelative_map :
    (postnikovCellImageForwardRelative R B C D P n hn b f g).hom ≫ Path.map R
      (SquareZero.baseChangeMap ((b ≫ postnikovMap R f n) ≫ postnikovMap R g n)
        (postnikovShiftedLayerBimodule R D n hn 1)) =
    (postnikovCellClassOverNaturalityWitness R B C P n hn b f).hom ≫
      Path.map R (postnikovDerivationTargetMap R g n hn) := by
  change ((postnikovCellImageRelative R B C P n hn b f).hom ≫
    Path.map R (postnikovCellImageForwardMap R B C D P n hn b f g)) ≫ _ = _
  rw [Category.assoc, ← Path.map_comp, postnikovCellImageForwardMap_map,
    Path.map_comp, ← Category.assoc, postnikovCellImageRelative_map]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
