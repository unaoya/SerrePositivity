module

public import SerrePositivity.BhattScholze.Semiperfectoid.RootedExtension.CompatibleRoot.CompatibleRootIdeal
public import SerrePositivity.CommutativeAlgebra.CompatibleRootIdealFlat

public meta import Batteries.Tactic.Alias

/-! # 共通層へ移した根・完全係数環のAPIの互換入口

既存のBS宣言名を保ち、証明は共通層の同じ宣言を再利用する。
-/

@[expose] public section
namespace SerrePositivity.BhattScholze
alias compatibleRoot_annihilator_le_succ := SerrePositivity.compatibleRoot_annihilator_le_succ
alias compatibleRoot_transition_kills_kernel := SerrePositivity.compatibleRoot_transition_kills_kernel
alias compatibleRootIdeal_flat := SerrePositivity.compatibleRootIdeal_flat
end SerrePositivity.BhattScholze
