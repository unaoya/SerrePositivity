module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.MixedHomBifunctor
public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.MixedBiresolutionComparison

/-!
# 中断した任意モデル源への一般化：OrdinaryResolutionPairs

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：The same raw mixed Hom on ordinary resolution pairs。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0255][inventory]を参照する。

[inventory]: ../../../../formalization-plans/k-theory-generalization-inventory.md#m0255
[plan]: ../../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The same raw mixed Hom on ordinary resolution pairs

Outer-frame choices are forgotten strictly. All actual inner resolution maps
and base maps are retained; no section or cofinality of forgetting is claimed.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra Opposite

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryResolutionPairs
variable {C : Type u} [Category.{v} C] [ModelCategory C]

abbrev Index := (ResolutionObject C)ᵒᵖ × (ResolutionObject Cᵒᵖ)ᵒᵖ
abbrev projection : Index (C := C) ⥤ Cᵒᵖ × C :=
  ResolutionObject.projection.op.prod (ResolutionObject.projection.op ⋙ unopUnop C)

abbrev diagrams : Index (C := C) ⥤
    (SimplexCategory ⥤ C)ᵒᵖ × (SimplexCategory ⥤ Cᵒᵖ)ᵒᵖ :=
  ResolutionObject.diagrams.op.prod (ResolutionObject.diagrams (C := Cᵒᵖ)).op
abbrev raw : Index (C := C) ⥤ SSet.{v} := diagrams ⋙ MixedDiagonalHom.functor

abbrev forgetFrames : RightResolutionMapping.Index C ⥤ Index (C := C) :=
  FramedResolution.forget.op.prod (FramedResolution.forget (C := Cᵒᵖ)).op

lemma projection_eq : forgetFrames (C := C) ⋙ projection = RightResolutionMapping.projection := rfl
lemma raw_eq : forgetFrames (C := C) ⋙ raw = MixedBiresolutionComparison.functor := rfl

lemma raw_map {X Y : Index (C := C)} (f : X ⟶ Y) :
    (raw (C := C)).map f = MixedDiagonalHom.map f.1.unop.diagram f.2.unop.diagram := rfl

end SerrePositivity.HomotopyFunctionComplex.OrdinaryResolutionPairs
