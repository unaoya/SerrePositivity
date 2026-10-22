module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovClassBaseZeroIso
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRestrictionEqualityIso

/-!
概要：元の class の共通底係数を、等しい指定零底への制限係数へ実同型で移す。
方針：既存の零底同型と、底射等式による同型を合成して二射影を保つ。
規約：底射の等式を明示入力する。使われ方：元の分母側の全経路比較。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (B P : Mon (Complex R)) [B.X.IsStrictlyLE 0]
  (n : ℤ) (hn : 0 ≤ n) (s : ℤ) (b : P ⟶ postnikov R B n) (q : P ⟶ postnikov R B 0)
  (hb : b ≫ postnikovTransition R B n 0 hn = q)

def postnikovClassZeroRebaseIso :
    SquareZero.algebra P (bimoduleRestrict b (postnikovShiftedLayerBimodule R B n hn s)) ≅
    SquareZero.algebra P (bimoduleRestrict q
      (DGBimoduleShift.obj (postnikovLayerZeroBimodule R B n) s)) :=
  postnikovClassBaseZeroIso R B P n hn s b ≪≫
    SquareZero.restrictionEqualityIso hb (DGBimoduleShift.obj (postnikovLayerZeroBimodule R B n) s)

lemma postnikovClassZeroRebaseIso_projection :
    (postnikovClassZeroRebaseIso R B P n hn s b q hb).hom ≫ SquareZero.projection _ _ =
      SquareZero.projection _ _ :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun t => (postnikovClassBaseZeroIso R B P n hn s b).hom ≫ t)
      (SquareZero.restrictionEqualityIso_projection hb _)).trans
      (postnikovClassBaseZeroIso_projection R B P n hn s b))

lemma postnikovClassZeroRebaseIso_map :
    (postnikovClassZeroRebaseIso R B P n hn s b q hb).hom ≫
      SquareZero.baseChangeMap q (DGBimoduleShift.obj (postnikovLayerZeroBimodule R B n) s) =
    SquareZero.baseChangeMap b (postnikovShiftedLayerBimodule R B n hn s) ≫
      postnikovClassToZeroBase R B n hn s :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun t => (postnikovClassBaseZeroIso R B P n hn s b).hom ≫ t)
      (SquareZero.restrictionEqualityIso_map hb _)).trans
      (postnikovClassBaseZeroIso_map R B P n hn s b))

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
