module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.RightResolutionMapping
public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.MixedResolutionLiftAction

/-!
概要：二つの bar 構成が共通に持つ小さい出力を一箇所で定義する。
方針：OrdinaryBarFirstAction と ResolutionBarFirstAction の一致する宣言をそのまま移す。
規約：元の変数・局所 Reedy instance を保持し、comma 添字圏を一般化しない。
使われ方：通常の resolution と framed resolution の bar 評価。
-/

@[expose] public section
noncomputable section
universe v u
open CategoryTheory HomotopicalAlgebra
namespace SerrePositivity.HomotopyFunctionComplex.BarOutput
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (R : RightResolutionMapping.Index C)
local instance : ModelCategory (SimplexCategory ⥤ C) := Reedy.simplexModelCategory C
local instance : ModelCategory (SimplexCategory ⥤ Cᵒᵖ) := Reedy.simplexModelCategory Cᵒᵖ
abbrev output : SSet.{v} := MixedResolutionLiftAction.output R.1.unop.inner R.2.unop.inner
end SerrePositivity.HomotopyFunctionComplex.BarOutput
