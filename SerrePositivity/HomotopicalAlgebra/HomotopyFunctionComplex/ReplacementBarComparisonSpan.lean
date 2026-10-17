module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ReplacementBarCandidate
public import SerrePositivity.HomotopicalAlgebra.Simplicial.RelativeBarSpan

/-!
# 中断した任意モデル源への一般化：ReplacementBarComparisonSpan

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：An actual natural span comparing replacement mapping spaces and the strict auxiliary bar。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0271][inventory]を参照する。

[inventory]: ../../../formalization-plans/k-theory-generalization-inventory.md#m0271
[plan]: ../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# An actual natural span comparing replacement mapping spaces and the strict auxiliary bar

The small mapping spaces enter by their explicit universe lift. Both legs
are actual natural transformations before localization. Their weak equivalence,
and a final small base functor, remain separate requirements.
-/

@[expose] public section
universe v u
noncomputable section
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.ReplacementMapping
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

abbrev auxiliaryMiddle : Index C ⥤ SSet.{max u v} :=
  BarConstruction.spanMiddle (projection (C := C)) (uncurried hcof hfib)

abbrev auxiliaryLeft : auxiliaryMiddle (C := C) hcof hfib ⟶
    uncurried hcof hfib ⋙ SSet.uliftFunctor.{max u v, v} :=
  BarConstruction.spanLeft (projection (C := C)) (uncurried hcof hfib)

abbrev auxiliaryRight : auxiliaryMiddle (C := C) hcof hfib ⟶
    projection (C := C) ⋙ auxiliaryBar hcof hfib :=
  BarConstruction.spanRight (projection (C := C)) (uncurried hcof hfib)

abbrev auxiliarySection (X : Index C) :
    SSet.uliftFunctor.{max u v, v}.obj ((uncurried hcof hfib).obj X) ⟶
      (auxiliaryMiddle (C := C) hcof hfib).obj X :=
  BarConstruction.spanSection (projection (C := C)) (uncurried hcof hfib) X

lemma auxiliarySection_retract (X : Index C) :
    auxiliarySection hcof hfib X ≫ (auxiliaryLeft (C := C) hcof hfib).app X = 𝟙 _ :=
  BarConstruction.spanSection_retract (projection (C := C)) (uncurried hcof hfib) X

end SerrePositivity.HomotopyFunctionComplex.ReplacementMapping
