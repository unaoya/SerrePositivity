module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCellClassOverImage
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeWitness

/-!
概要：元の係数像の自然性経路を、その全射を保つ相対証人として取り出す。
方針：既存 ImageWitness の全底経路と底変更射影をそのまま使う。
規約：新しい経路を選ばない。使われ方：貼合せと affine 二段自然性の全経路照合。
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

def postnikovCellImageRelative : SquareZero.RelativeWitness
    (cellAugmentation R (cellResolution R P) ≫ cellAugmentation R P)
    (bimoduleRestrict (b ≫ postnikovMap R f n) (postnikovShiftedLayerBimodule R C n hn 1))
    (cellAugmentation R (cellResolution R P) ≫ postnikovCellClassOver R B P n hn b ≫
      SquareZero.coefficientMap P (postnikovCellClassOverCoefficient R B C P n hn b f))
    (cellAugmentation R (cellResolution R P) ≫
      postnikovCellClassOver R C P n hn (b ≫ postnikovMap R f n)) where
  toWitness := postnikovCellClassOverImageWitness R B C P n hn b f
  projection_eq := postnikovCellClassOverImageWitness_relative R B C P n hn b f

lemma postnikovCellImageRelative_hom : (postnikovCellImageRelative R B C P n hn b f).hom =
    (postnikovCellClassOverImageWitness R B C P n hn b f).hom := rfl

/-- 底変更した経路の全射影は、元の class 自然性経路。 -/
lemma postnikovCellImageRelative_map :
    (postnikovCellImageRelative R B C P n hn b f).hom ≫
      Path.map R (SquareZero.baseChangeMap (b ≫ postnikovMap R f n)
        (postnikovShiftedLayerBimodule R C n hn 1)) =
    (postnikovCellClassOverNaturalityWitness R B C P n hn b f).hom := by
  change (postnikovCellClassOverRelativeWitness R B C P n hn b f).hom ≫ _ = _
  unfold postnikovCellClassOverRelativeWitness
  exact SquareZero.baseChangeWitness_map _ _ _ _ _ _ _ _ _

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
