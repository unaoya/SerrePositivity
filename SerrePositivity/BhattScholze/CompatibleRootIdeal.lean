module

public import SerrePositivity.CommutativeAlgebra.CompatibleRootIdeal

public meta import Batteries.Tactic.Alias

/-! # 共通層へ移した根・完全係数環のAPIの互換入口

既存のBS宣言名を保ち、証明は共通層の同じ宣言を再利用する。
-/

@[expose] public section
namespace SerrePositivity.BhattScholze
alias compatibleRootIdeal := SerrePositivity.compatibleRootIdeal
alias span_root_zero_le_compatibleRootIdeal := SerrePositivity.span_root_zero_le_compatibleRootIdeal
alias compatibleRoot_principal_monotone := SerrePositivity.compatibleRoot_principal_monotone
alias mem_compatibleRootIdeal_iff := SerrePositivity.mem_compatibleRootIdeal_iff
alias compatibleRootIdeal_mul_self := SerrePositivity.compatibleRootIdeal_mul_self
alias compatibleRootIdeal_le_ker_of_root_zero := SerrePositivity.compatibleRootIdeal_le_ker_of_root_zero
alias compatibleRootIdeal_map := SerrePositivity.compatibleRootIdeal_map
-- Preserve rewriting through the former computational definitions.
attribute [reducible] compatibleRootIdeal
end SerrePositivity.BhattScholze
