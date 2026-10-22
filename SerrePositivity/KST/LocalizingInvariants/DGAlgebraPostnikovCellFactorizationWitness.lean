module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCellFactorizationTarget
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeWitnessBaseChange
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeWitnessPrecomp

/-!
概要：二段自然性の class 経路を、因子分解によらない両端と同じ P 上へ移す。
方針：元の実合成経路を後合成し、四重 augmentation の底へ厳密に底変更する。
規約：両端の相対模型を因子分解ごとに選び直さない。使われ方：右自然性正方形。
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

def postnikovCellFactorizationCommonSource : cellResolution R (cellResolution R
    (cellResolution R (cellResolution R P))) ⟶ SquareZero.algebra P
      (bimoduleRestrict (b ≫ postnikovMap R h n) (postnikovShiftedLayerBimodule R D n hn 1)) :=
  SquareZero.baseChangeLift (b ≫ postnikovMap R h n) (postnikovShiftedLayerBimodule R D n hn 1)
    (postnikovCellFactorizationProjection R P) (postnikovCellFactorizationSource R B D P n hn b h)
    (postnikovCellFactorizationSource_projection R B D P n hn b h)

def postnikovCellFactorizationCommonTarget : cellResolution R (cellResolution R
    (cellResolution R (cellResolution R P))) ⟶ SquareZero.algebra P
      (bimoduleRestrict (b ≫ postnikovMap R h n) (postnikovShiftedLayerBimodule R D n hn 1)) :=
  SquareZero.baseChangeLift (b ≫ postnikovMap R h n) (postnikovShiftedLayerBimodule R D n hn 1)
    (postnikovCellFactorizationProjection R P) (postnikovCellFactorizationTarget R B D P n hn b h)
    (postnikovCellFactorizationTarget_projection R B D P n hn b h)

variable (C : Mon (Complex R)) [C.X.IsStrictlyLE 0]
  (f : B ⟶ C) (g : C ⟶ D) (heq : f ≫ g = h)

def postnikovCellFactorizationClassWitness : SquareZero.RelativeWitness
    (postnikovCellFactorizationProjection R P ≫ (b ≫ postnikovMap R h n))
    (postnikovShiftedLayerBimodule R D n hn 1)
    (postnikovCellFactorizationSource R B D P n hn b h)
    (postnikovCellFactorizationTarget R B D P n hn b h) :=
  (SquareZero.cellClassWitness R (postnikovPerturbedProjection R D n hn)
    (postnikovCellLiftFactorizationWitness R B C D P n hn b h f g heq)
    (postnikovCellLiftFactorizationWitness_relative R B C D P n hn b h f g heq)
    (postnikovShiftedLayerBimodule R D n hn 1) (postnikovPerturbedClass R D n hn)
    (postnikovPerturbedClass_projection R D n hn)).rebase
      (postnikovCellFactorization_base R B D P n hn b h)

def postnikovCellFactorizationCommonWitness : SquareZero.RelativeWitness
    (postnikovCellFactorizationProjection R P)
    (bimoduleRestrict (b ≫ postnikovMap R h n) (postnikovShiftedLayerBimodule R D n hn 1))
    (postnikovCellFactorizationCommonSource R B D P n hn b h)
    (postnikovCellFactorizationCommonTarget R B D P n hn b h) :=
  SquareZero.baseChangeRelativeWitness (b ≫ postnikovMap R h n)
    (postnikovShiftedLayerBimodule R D n hn 1) (postnikovCellFactorizationProjection R P)
    (postnikovCellFactorizationClassWitness R B D P n hn b h C f g heq)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
