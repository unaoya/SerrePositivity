module

public import SerrePositivity.BhattScholze.CompatibleRootIdealFlat
public import SerrePositivity.CommutativeAlgebra.CompatibleRootIdealTensor

public meta import Batteries.Tactic.Alias

/-! # 共通層へ移した根・完全係数環のAPIの互換入口

既存のBS宣言名を保ち、証明は共通層の同じ宣言を再利用する。
-/

@[expose] public section
namespace SerrePositivity.BhattScholze
alias compatibleRootIdealElement := SerrePositivity.compatibleRootIdealElement
alias compatibleRootIdeal_tensor_singleStage := SerrePositivity.compatibleRootIdeal_tensor_singleStage
alias compatibleRootIdealTensorMap := SerrePositivity.compatibleRootIdealTensorMap
alias compatibleRootIdealTensorMap_tmul := SerrePositivity.compatibleRootIdealTensorMap_tmul
attribute [simp] compatibleRootIdealTensorMap_tmul
alias compatibleRootIdealTensorMap_injective := SerrePositivity.compatibleRootIdealTensorMap_injective
-- Preserve rewriting through the former computational definitions.
attribute [reducible] compatibleRootIdealElement compatibleRootIdealTensorMap
end SerrePositivity.BhattScholze
