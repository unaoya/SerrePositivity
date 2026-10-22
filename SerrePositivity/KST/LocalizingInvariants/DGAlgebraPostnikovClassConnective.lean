module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraConnectiveQuasiIso
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovClassModelMap

/-!
概要：元の Postnikov class の経路模型の connective 性を供給する。
方針：元の隣接切断からの実準同型比較で connective 性を輸送する。
規約：模型の置き換えや値の可逆性は入力しない。使われ方：実 class 比較の反転。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (B : Mon (Complex R)) [B.X.IsStrictlyLE 0]
  (n : ℤ) (hn : 0 ≤ n)

lemma postnikovClassModel_isConnective : IsConnective R (postnikovClassModel R B n hn) :=
  (quasiIso_isConnective_iff R (postnikovHomotopyPullbackComparison R B n hn)
    (postnikovHomotopyPullbackComparison_quasiIso R B n hn)).1
      (postnikov_isConnective R B (n + 1))

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
