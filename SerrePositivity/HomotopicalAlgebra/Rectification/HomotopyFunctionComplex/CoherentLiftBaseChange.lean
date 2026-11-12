module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.CoherentLiftRelative
public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ResolutionLiftFunctorLaws

/-!
# 中断した任意モデル源への一般化：CoherentLiftBaseChange

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Actual base change of coherent lift tuples and their interpolation。

## 方針（定義・証明）
全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0064][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0064
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Actual base change of coherent lift tuples and their interpolation
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.CoherentLiftBaseChange
variable {C : Type u} [Category.{v} C] [ModelCategory C]

def strict {X Y : ResolutionObject C} {f g : X.base ⟶ Y.base} (h : f = g)
    (k : CoherentLiftTuples.StrictLift X Y f) : CoherentLiftTuples.StrictLift X Y g :=
  ⟨k.val, k.property.trans h⟩

def tuples {X Y : ResolutionObject C} {f g : X.base ⟶ Y.base} (h : f = g) :
    CoherentLiftTuples.obj X Y f ⟶ CoherentLiftTuples.obj X Y g := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.VertexTuples.map (strict h)

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)

lemma interpolation {X Y : ResolutionObject C} {f g : X.base ⟶ Y.base} (h : f = g) :
    CoherentLiftTuples.interpolation hcof X Y f ≫ ResolutionLiftSpace.baseChange h =
      tuples h ≫ CoherentLiftTuples.interpolation hcof X Y g := by
  cases h
  change _ ≫ (𝟙 _) = (𝟙 _) ≫ _
  rw [Category.comp_id, Category.id_comp]

end SerrePositivity.HomotopyFunctionComplex.CoherentLiftBaseChange
