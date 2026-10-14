module

public import SerrePositivity.CLMST.CyclicLength

/-! # 巡回長さ零の旧公開入口（互換alias）

実際の証明はCLMST/CyclicLengthに置く。
ここにはCLMSTの数値結論のsorryを保持せず、既存importと公開名の互換性だけを保つ。
深い全射性の文献入力はBhattScholze/Inputs/SemiperfectoidSurjectivityで明示する。
-/

public section
namespace SerrePositivity.CLMST.Inputs

alias cyclic_length_eq_zero_of_not_dvd := SerrePositivity.CLMST.cyclic_length_eq_zero_of_not_dvd
alias cyclic_length_eq_zero := SerrePositivity.CLMST.cyclic_length_eq_zero

end SerrePositivity.CLMST.Inputs
