module

public import Mathlib.CategoryTheory.Groupoid.Basic

/-!
# 元の groupoid の射の右合成による Hom の同値

概要：元の射の右合成をその元の逆射で戻す。
方針：元の結合則と逆射の両公理を使う。
規約：単位の前合成を追加せず、元の合成そのものを順方向とする。
使われ方：根付き被覆の持ち上げ射のファイバー間の同値。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

def groupoidPostcomposeEquiv {G : Type u} [Groupoid.{v} G] (S : G) {X Y : G} (f : X ⟶ Y) :
    (S ⟶ X) ≃ (S ⟶ Y) where
  toFun p := p ≫ f
  invFun p := p ≫ inv f
  left_inv p := by simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  right_inv p := by simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
