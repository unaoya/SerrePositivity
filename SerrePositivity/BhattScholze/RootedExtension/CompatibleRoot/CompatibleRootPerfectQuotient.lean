module

public import SerrePositivity.BhattScholze.RootedExtension.CompatibleRoot.CompatibleRootIdeal
public import SerrePositivity.CommutativeAlgebra.CompatibleRootPerfectQuotient

public meta import Batteries.Tactic.Alias

/-! # 共通層へ移した根・完全係数環のAPIの互換入口

既存のBS宣言名を保ち、証明は共通層の同じ宣言を再利用する。
-/

@[expose] public section
namespace SerrePositivity.BhattScholze
alias compatibleRootIdeal_map_frobenius_eq := SerrePositivity.compatibleRootIdeal_map_frobenius_eq
alias compatibleRootQuotient_perfectRing := SerrePositivity.compatibleRootQuotient_perfectRing
end SerrePositivity.BhattScholze
