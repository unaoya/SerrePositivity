module

public import SerrePositivity.BhattScholze.CompatibleRootIdealTensor
public import SerrePositivity.HomologicalAlgebra.CompatibleRootQuotientTor

public meta import Batteries.Tactic.Alias

/-! # 共通層へ移した根・完全係数環のAPIの互換入口

既存のBS宣言名を保ち、証明は共通層の同じ宣言を再利用する。
-/

@[expose] public section
namespace SerrePositivity.BhattScholze
alias compatibleRootQuotient_tor_subsingleton := SerrePositivity.compatibleRootQuotient_tor_subsingleton
alias compatibleRootQuotient_derivedTensor_concentrated := SerrePositivity.compatibleRootQuotient_derivedTensor_concentrated
end SerrePositivity.BhattScholze
