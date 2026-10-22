module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCellFactorizationImageIso
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRestrictionEqualityInverse

/-!
概要：因子分解の係数表示を移す実同型の逆について、元の二射影を公開する。
方針：一般の底射等式の同型の逆を、同じ明示的な底射へ適用する。
規約：定義展開による Γ データの再計算を避ける。使われ方：元の T の全経路照合。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (B D P : Mon (Complex R))
  [B.X.IsStrictlyLE 0] [D.X.IsStrictlyLE 0]
  (n : ℤ) (hn : 0 ≤ n) (b : P ⟶ postnikov R B n) (h : B ⟶ D)
  (C : Mon (Complex R)) [C.X.IsStrictlyLE 0]
  (f : B ⟶ C) (g : C ⟶ D) (heq : f ≫ g = h)

lemma postnikovCellFactorizationImageIso_inv_projection :
    (postnikovCellFactorizationImageIso R B D P n hn b h C f g heq).inv ≫
      SquareZero.projection _ _ = SquareZero.projection _ _ :=
  SquareZero.restrictionEqualityIso_inv_projection
    (postnikovCellFactorizationImage_base R B D P n b h C f g heq)
    (postnikovShiftedLayerBimodule R D n hn 1)

lemma postnikovCellFactorizationImageIso_inv_map :
    (postnikovCellFactorizationImageIso R B D P n hn b h C f g heq).inv ≫
      SquareZero.baseChangeMap (b ≫ postnikovMap R h n)
        (postnikovShiftedLayerBimodule R D n hn 1) =
      SquareZero.baseChangeMap ((b ≫ postnikovMap R f n) ≫ postnikovMap R g n)
        (postnikovShiftedLayerBimodule R D n hn 1) :=
  SquareZero.restrictionEqualityIso_inv_map
    (postnikovCellFactorizationImage_base R B D P n b h C f g heq)
    (postnikovShiftedLayerBimodule R D n hn 1)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
