module

public import SerrePositivity.CommutativeAlgebra.PerfectCoefficientTensor

public meta import Batteries.Tactic.Alias

/-! # 共通層へ移した根・完全係数環のAPIの互換入口

既存のBS宣言名を保ち、証明は共通層の同じ宣言を再利用する。
-/

@[expose] public section
namespace SerrePositivity.BhattScholze
alias coefficientTensorLift := SerrePositivity.coefficientTensorLift
alias coefficientTensorLift_tmul := SerrePositivity.coefficientTensorLift_tmul
alias perfectCoefficientTensorRoot := SerrePositivity.perfectCoefficientTensorRoot
alias perfectCoefficientTensorRoot_tmul := SerrePositivity.perfectCoefficientTensorRoot_tmul
alias perfectCoefficientTensor_perfectRing := SerrePositivity.perfectCoefficientTensor_perfectRing

-- Preserve rewriting through the former computational definitions.
attribute [reducible] coefficientTensorLift perfectCoefficientTensorRoot
end SerrePositivity.BhattScholze
