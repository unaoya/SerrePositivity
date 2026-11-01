module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ReplacementBarComparisonSpan
public import SerrePositivity.HomotopicalAlgebra.Simplicial.RelativeBarSpanContraction

/-!
# 中断した任意モデル源への一般化：ReplacementBarLeftContraction

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：The chosen left comparison leg has an actual simplicial homotopy inverse。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0272][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0272
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The chosen left comparison leg has an actual simplicial homotopy inverse

This contracts the whole auxiliary diagonal. It does not assume a model
structure on the larger simplicial-set universe or assert the final small descent.
-/

@[expose] public section
universe v u
noncomputable section
open CategoryTheory HomotopicalAlgebra

namespace SerrePositivity.HomotopyFunctionComplex.ReplacementMapping
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

abbrev auxiliaryLeftHomotopy (X : Index C) :
    SSet.Homotopy (𝟙 ((auxiliaryMiddle hcof hfib).obj X))
      ((auxiliaryLeft hcof hfib).app X ≫ auxiliarySection hcof hfib X) :=
  SimplicialModel.BarConstruction.spanLeftHomotopy (projection (C := C))
    (uncurried hcof hfib) X

/-- The same actual section and all-degree homotopy witness the left inverse data. -/
theorem auxiliaryLeft_has_homotopyInverse (X : Index C) :
    ∃ s : SSet.uliftFunctor.{max u v, v}.obj ((uncurried hcof hfib).obj X) ⟶
      (auxiliaryMiddle hcof hfib).obj X,
      s ≫ (auxiliaryLeft hcof hfib).app X = 𝟙 _ ∧
        Nonempty (SSet.Homotopy (𝟙 _) ((auxiliaryLeft hcof hfib).app X ≫ s)) :=
  ⟨auxiliarySection hcof hfib X, auxiliarySection_retract hcof hfib X,
    ⟨auxiliaryLeftHomotopy hcof hfib X⟩⟩

end SerrePositivity.HomotopyFunctionComplex.ReplacementMapping
