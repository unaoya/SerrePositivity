module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ReplacementBarLeftContraction
public import SerrePositivity.HomotopicalAlgebra.Simplicial.RelativeBarAnodyneComparison

/-!
# 中断した任意モデル源への一般化：ReplacementBarAnodyneComparison

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Natural anodyne-localized comparison for the actual auxiliary left bar leg。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0269][inventory]を参照する。

[inventory]: ../../../formalization-plans/k-theory-generalization-inventory.md#m0269
[plan]: ../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Natural anodyne-localized comparison for the actual auxiliary left bar leg
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

/-- No model on SSet[max(u,v)] is an input to this comparison of whole diagrams. -/
abbrev auxiliaryLeftAnodyneIso :
    auxiliaryMiddle (C := C) hcof hfib ⋙ AnodyneHomotopy.anodyneQ ≅
      (uncurried hcof hfib ⋙ SSet.uliftFunctor.{max u v, v}) ⋙ AnodyneHomotopy.anodyneQ :=
  BarConstruction.spanLeftAnodyneIso (projection (C := C)) (uncurried hcof hfib)

lemma auxiliaryLeftAnodyneIso_hom_app (X : Index C) :
    (auxiliaryLeftAnodyneIso hcof hfib).hom.app X =
      AnodyneHomotopy.anodyneQ.map ((auxiliaryLeft hcof hfib).app X) := rfl

end SerrePositivity.HomotopyFunctionComplex.ReplacementMapping
