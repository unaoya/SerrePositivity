module

public import SerrePositivity.HomotopicalAlgebra.Rectification.CategoryTheory.AnchoredChainTransport
public import Mathlib.CategoryTheory.Elements

/-!
# 中断した任意モデル源への一般化：ArrowContext

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：One category of changing central arrows and its actual factorization parameters。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0006][inventory]を参照する。

[inventory]: ../../../../formalization-plans/k-theory-generalization-inventory.md#m0006
[plan]: ../../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# One category of changing central arrows and its actual factorization parameters

Objects are actual arrows. A morphism changes the source contravariantly
and the target covariantly, recording the equation for the new center.
This is the category of elements of the ordinary Hom bifunctor.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.ArrowContext
variable (D : Type u) [Category.{v} D]

abbrev homs : Dᵒᵖ × D ⥤ Type v := Functor.uncurry.obj coyoneda
abbrev Index := (homs D).Elements
abbrev projection : Index D ⥤ Dᵒᵖ × D := Functor.Elements.π (homs D)

variable {D}
abbrev source (q : Index D) : D := q.obj.1.unop
abbrev target (q : Index D) : D := q.obj.2
abbrev arrow (q : Index D) : source q ⟶ target q := q.val
abbrev ofArrow {X Y : D} (f : X ⟶ Y) : Index D := (homs D).elementsMk (Opposite.op X, Y) f

lemma equation {q r : Index D} (f : q ⟶ r) :
    (f.hom.1.unop ≫ arrow q) ≫ f.hom.2 = arrow r := f.map_val

/-- Actual transport of factorization categories as the center changes. -/
abbrev factorizationMap {q r : Index D} (f : q ⟶ r) :
    ArrowFactorization (arrow q) ⥤ ArrowFactorization (arrow r) :=
  ArrowFactorization.transport (arrow q) f.hom.1.unop f.hom.2 (arrow r) (equation f)

variable (D)
/-- All changing-center factorization categories in one strict diagram. -/
def factorizations : Index D ⥤ Cat.{v, max u v} where
  obj q := Cat.of (ArrowFactorization (arrow q))
  map f := (factorizationMap f).toCatHom
  map_id q := by
    apply Cat.Hom.ext
    exact ArrowFactorization.transport_id (arrow q)
  map_comp f g := by
    apply Cat.Hom.ext
    exact (ArrowFactorization.transport_comp _ _ _ _ (equation f) _ _ _ (equation g)).symm


/-- One whole chain parameter diagram, for all centers and all simplicial operators. -/
def parameters : Index D ⥤ SSet.{max u v} where
  obj q := AnchoredChain.simplicial (arrow q)
  map f := AnchoredChain.mapFunctor (factorizationMap f)
  map_id q := by
    change AnchoredChain.mapFunctor (ArrowFactorization.transport (arrow q)
      (𝟙 _) (𝟙 _) (arrow q) _) = _
    rw [ArrowFactorization.transport_id, AnchoredChain.mapFunctor_id]
  map_comp f g := (AnchoredChain.mapFunctor_comp _ _).trans
    (congrArg (fun F => AnchoredChain.mapFunctor F)
      (ArrowFactorization.transport_comp _ _ _ _ (equation f) _ _ _ (equation g))) |>.symm

lemma parameters_diagram {q r : Index D} (f : q ⟶ r) {n : ℕ} (c : AnchoredChain (arrow q) n) :
    (((parameters D).map f).app (Opposite.op (SimplexCategory.mk n)) c).diagram = c.diagram :=
  AnchoredChain.transport_diagram _ _ _ _ (equation f) c

lemma parameters_cut {q r : Index D} (f : q ⟶ r) {n : ℕ}
    (c : AnchoredChain (arrow q) n) (j : Fin (n + 1)) :
    (((parameters D).map f).app (Opposite.op (SimplexCategory.mk n)) c).cut j =
      (factorizationMap f).obj (c.cut j) := AnchoredChain.mapFunctor_cut _ c j

end SerrePositivity.ArrowContext
