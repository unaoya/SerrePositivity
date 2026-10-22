module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRestrictionEqualityIso
public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCellAffineFactorizationSquare

/-!
概要：因子分解によらない係数表示を、元の二 ImageWitness の合成係数へ同定する。
方針：合成底射の等式による実平方零同型と、底変更経路の元の射影を使う。
規約：全自然性経路を保持。使われ方：四重 cell 上の affine 経路の具体的照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (B D P : Mon (Complex R))
  [B.X.IsStrictlyLE 0] [D.X.IsStrictlyLE 0]
  (n : ℤ) (hn : 0 ≤ n) (b : P ⟶ postnikov R B n) (h : B ⟶ D)
  (C : Mon (Complex R)) [C.X.IsStrictlyLE 0]
  (f : B ⟶ C) (g : C ⟶ D) (heq : f ≫ g = h)

include heq in
lemma postnikovCellFactorizationImage_base : b ≫ postnikovMap R h n =
    (b ≫ postnikovMap R f n) ≫ postnikovMap R g n := by
  rw [← heq, postnikovMap_composition, Category.assoc]

def postnikovCellFactorizationImageIso :=
  SquareZero.restrictionEqualityIso (postnikovCellFactorizationImage_base
    R B D P n b h C f g heq) (postnikovShiftedLayerBimodule R D n hn 1)

lemma postnikovCellFactorizationImageIso_projection :
    (postnikovCellFactorizationImageIso R B D P n hn b h C f g heq).hom ≫
      SquareZero.projection _ _ = SquareZero.projection _ _ :=
  SquareZero.restrictionEqualityIso_projection _ _

lemma postnikovCellFactorizationImageIso_map :
    (postnikovCellFactorizationImageIso R B D P n hn b h C f g heq).hom ≫
      SquareZero.baseChangeMap ((b ≫ postnikovMap R f n) ≫ postnikovMap R g n)
        (postnikovShiftedLayerBimodule R D n hn 1) =
      SquareZero.baseChangeMap (b ≫ postnikovMap R h n)
        (postnikovShiftedLayerBimodule R D n hn 1) :=
  SquareZero.restrictionEqualityIso_map _ _

lemma postnikovCellFactorizationImageClass_map :
    ((postnikovCellFactorizationAffineCommonWitness R B D P n hn b h C f g heq).hom ≫
      Path.map R (postnikovCellFactorizationImageIso R B D P n hn b h C f g heq).hom) ≫
      Path.map R (SquareZero.baseChangeMap
        ((b ≫ postnikovMap R f n) ≫ postnikovMap R g n)
        (postnikovShiftedLayerBimodule R D n hn 1)) =
      (postnikovCellCompositionClassAffine R B C D P n hn b f g).hom := by
  rw [Category.assoc, ← Path.map_comp, postnikovCellFactorizationImageIso_map]
  change (SquareZero.baseChangeRelativeWitness (b ≫ postnikovMap R h n)
    (postnikovShiftedLayerBimodule R D n hn 1) (postnikovCellFactorizationProjection R P)
    (postnikovCellFactorizationAffineWitness R B D P n hn b h C f g heq)).hom ≫ _ = _
  rw [SquareZero.baseChangeRelativeWitness_map]
  rfl

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
