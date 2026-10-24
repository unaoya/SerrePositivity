module
public import SerrePositivity.InfinityCategories.Stable.UniverseExactFunctor
public import SerrePositivity.InfinityCategories.Stable.UniverseZeroTriangle
/-!
概要：完全関手は単体集合の宇宙持ち上げ後にも完全である。
方針：任意の持ち上げ先の零角四角形を全写像の同値で降下し、保存後に戻す。
規約：安定性や模型圏の仮定を追加しない。既存の降下方向は変更しない。
使われ方：異なる対象宇宙の dg 加群値関手を共通宇宙で比較する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial

/-- 完全関手の零頂点保存と全 cofiber 保存を任意の上位宇宙へ持ち上げる。 -/
theorem isExactFunctor_ulift {X Y : SSet.{u}} (F : X ⟶ Y) (h : IsExactFunctor F) :
    IsExactFunctor ((SSet.uliftFunctor.{v, u}).map F) where
  preservesZero x hx := by
    let := h
    exact (isZeroVertex_iff_ulift.{u, v} _).1
      (IsExactFunctor.preservesZero (F := F) x.down
        ((isZeroVertex_iff_ulift.{u, v} x.down).2 hx))
  preservesCofiber t ht := by
    let := h
    have hp := (isPushoutSquare_iff_ulift.{u, v} (t.down.square ≫ F)).1
      (IsExactFunctor.preservesCofiber (F := F) t.down (t.isCofiber_down ht))
    rw [uliftSquare_postcomp, t.ulift_down_square] at hp
    exact hp

/-- 単体集合の宇宙持ち上げは完全性を保存かつ反映する。 -/
theorem isExactFunctor_iff_ulift {X Y : SSet.{u}} (F : X ⟶ Y) :
    IsExactFunctor F ↔ IsExactFunctor ((SSet.uliftFunctor.{v, u}).map F) :=
  ⟨isExactFunctor_ulift F, isExactFunctor_of_ulift F⟩

end SerrePositivity.InfinityCategories
