module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryResolutionRows
public import SerrePositivity.HomotopicalAlgebra.Simplicial.RelativeBarReindex
public import SerrePositivity.HomotopicalAlgebra.Simplicial.RelativeBarAnodyneComparison

/-!
# 中断した任意モデル源への一般化：OrdinaryResolutionBar

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：A strict ordinary-resolution bar with an actual comparison from the original framed bar。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0253][inventory]を参照する。

[inventory]: ../../../../formalization-plans/k-theory-generalization-inventory.md#m0253
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# A strict ordinary-resolution bar with an actual comparison from the original framed bar

The original raw mapping spaces factor strictly through forgetting outer frames.
The natural comparison span retains its old source, middle, and left leg.
No weak equivalence of the new right leg is asserted here.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryResolutionBar
variable {C : Type u} [Category.{v} C] [ModelCategory C]

abbrev functor : Cᵒᵖ × C ⥤ SSet.{max u v} :=
  BarConstruction.relative (OrdinaryResolutionPairs.projection (C := C)) OrdinaryResolutionPairs.raw
abbrev framed : Cᵒᵖ × C ⥤ SSet.{max u v} :=
  BarConstruction.relative (RightResolutionMapping.projection (C := C))
    MixedBiresolutionComparison.functor

/-- Every original comma chain is sent by the actual forgetful functor, with its original labels. -/
def comparison : framed (C := C) ⟶ functor :=
  BarConstruction.reindex OrdinaryResolutionPairs.forgetFrames OrdinaryResolutionPairs.projection
    OrdinaryResolutionPairs.raw

lemma comparison_label (b : Cᵒᵖ × C) (n : SimplexCategoryᵒᵖ)
    (c : ((framed (C := C)).obj b).obj n) (i : Fin (n.unop.len + 1)) :
    ((((comparison (C := C)).app b).app n c).obj i).left.val = (c.obj i).left.val := rfl

abbrev middle : RightResolutionMapping.Index C ⥤ SSet.{max u v} :=
  BarConstruction.spanMiddle (RightResolutionMapping.projection (C := C))
    MixedBiresolutionComparison.functor
abbrev left : middle (C := C) ⟶ MixedBiresolutionComparison.functor ⋙
    SSet.uliftFunctor.{max u v, v} :=
  BarConstruction.spanLeft (RightResolutionMapping.projection (C := C))
    MixedBiresolutionComparison.functor

def right : middle (C := C) ⟶ RightResolutionMapping.projection ⋙ functor :=
  BarConstruction.spanRight (RightResolutionMapping.projection (C := C))
    MixedBiresolutionComparison.functor ≫
      Functor.whiskerLeft RightResolutionMapping.projection comparison

/-- The old left comparison remains the actual natural isomorphism after anodyne inversion. -/
abbrev leftAnodyneIso : middle (C := C) ⋙ AnodyneHomotopy.anodyneQ ≅
    (MixedBiresolutionComparison.functor ⋙ SSet.uliftFunctor.{max u v, v}) ⋙
      AnodyneHomotopy.anodyneQ :=
  BarConstruction.spanLeftAnodyneIso (RightResolutionMapping.projection (C := C))
    MixedBiresolutionComparison.functor

lemma leftAnodyneIso_hom (R : RightResolutionMapping.Index C) :
    (leftAnodyneIso (C := C)).hom.app R =
      AnodyneHomotopy.anodyneQ.map ((left (C := C)).app R) := rfl

end SerrePositivity.HomotopyFunctionComplex.OrdinaryResolutionBar
