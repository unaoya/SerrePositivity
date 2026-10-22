module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCellFactorizationAffine
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCellFactorizationSquare
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeSquareComposition

/-!
概要：同じ射の二因子分解から得る affine class 合成を、元の共通底上で比較する。
方針：cell との比較を両側へ縦合成し、二因子分解の既存の実充填を使う。
規約：全 class 経路の一致を仮定しない。使われ方：Γ の右合成の自然性比較。
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
  (C C' : Mon (Complex R)) [C.X.IsStrictlyLE 0] [C'.X.IsStrictlyLE 0]
  (f : B ⟶ C) (g : C ⟶ D) (heq : f ≫ g = h)
  (f' : B ⟶ C') (g' : C' ⟶ D) (heq' : f' ≫ g' = h)

/-- 実 affine 合成どうしの、端点・全底射影を固定した二重経路。 -/
def postnikovCellAffineFactorizationSquare : SquareZero.RelativeWitnessSquare
    (postnikovCellFactorizationAffineWitness R B D P n hn b h C f g heq)
    (postnikovCellFactorizationAffineWitness R B D P n hn b h C' f' g' heq') :=
  ((postnikovCellFactorizationAffineSquare R B D P n hn b h C f g heq).symm.trans
    (postnikovCellFactorizationClassSquare R B D P n hn b h C C' f g heq f' g' heq')).trans
    (postnikovCellFactorizationAffineSquare R B D P n hn b h C' f' g' heq')

/-- 同じ P に底変更した元の affine 経路。 -/
def postnikovCellFactorizationAffineCommonWitness : SquareZero.RelativeWitness
    (postnikovCellFactorizationProjection R P)
    (bimoduleRestrict (b ≫ postnikovMap R h n) (postnikovShiftedLayerBimodule R D n hn 1))
    (postnikovCellFactorizationCommonSource R B D P n hn b h)
    (postnikovCellFactorizationCommonTarget R B D P n hn b h) :=
  SquareZero.baseChangeRelativeWitness (b ≫ postnikovMap R h n)
    (postnikovShiftedLayerBimodule R D n hn 1) (postnikovCellFactorizationProjection R P)
    (postnikovCellFactorizationAffineWitness R B D P n hn b h C f g heq)

/-- 元の cell 経路と affine 経路の比較も、同じ P と元の両端を保つ。 -/
def postnikovCellFactorizationAffineCommonSquare : SquareZero.RelativeWitnessSquare
    (postnikovCellFactorizationCommonWitness R B D P n hn b h C f g heq)
    (postnikovCellFactorizationAffineCommonWitness R B D P n hn b h C f g heq) :=
  SquareZero.baseChangeRelativeWitnessSquare (b ≫ postnikovMap R h n)
    (postnikovShiftedLayerBimodule R D n hn 1) (postnikovCellFactorizationProjection R P)
    (postnikovCellFactorizationAffineSquare R B D P n hn b h C f g heq)

def postnikovCellAffineFactorizationCommonSquare : SquareZero.RelativeWitnessSquare
    (postnikovCellFactorizationAffineCommonWitness R B D P n hn b h C f g heq)
    (postnikovCellFactorizationAffineCommonWitness R B D P n hn b h C' f' g' heq') :=
  SquareZero.baseChangeRelativeWitnessSquare (b ≫ postnikovMap R h n)
    (postnikovShiftedLayerBimodule R D n hn 1) (postnikovCellFactorizationProjection R P)
    (postnikovCellAffineFactorizationSquare R B D P n hn b h C C' f g heq f' g' heq')

/-- affine 合成からの元の二つの実模型輸送を結ぶ乗法的経路。 -/
def postnikovCellAffineFactorizationTransportHomotopy : Path.Witness R
    (SquareZeroExtension.transport
      (bimoduleRestrict (b ≫ postnikovMap R h n) (postnikovShiftedLayerBimodule R D n hn 1))
      (postnikovCellFactorizationAffineCommonWitness R B D P n hn b h C f g heq))
    (SquareZeroExtension.transport
      (bimoduleRestrict (b ≫ postnikovMap R h n) (postnikovShiftedLayerBimodule R D n hn 1))
      (postnikovCellFactorizationAffineCommonWitness R B D P n hn b h C' f' g' heq')) :=
  SquareZeroExtension.transportHomotopy _
    (postnikovCellAffineFactorizationCommonSquare R B D P n hn b h C C' f g heq f' g' heq')

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
