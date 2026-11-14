module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.CoproductCylinderMap

/-!
概要：定値な二円柱を貼ると、直和上の定値円柱になる。
方針：両枝への制限と二つの指定射を照合する。
規約：全時刻の厳密な等式。
使われ方：端点固定の path 比較を引き戻し内の比較へ移す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 概要：定値な両枝の貼り合わせは直和上で時間を忘れる。
方針：両枝で第一射影の自然性と直和の式を使う。
規約：任意の形状。使われ方：定値な境界円柱の同定。 -/
lemma coprodCylinderMap_constant {A C X : SSet.{u}} (f : A ⟶ X) (g : C ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coprodCylinderMap (fst A (Δ[1] : SSet.{u}) ≫ f) (fst C (Δ[1] : SSet.{u}) ≫ g) =
      fst (A ⨿ C) (Δ[1] : SSet.{u}) ≫ coprod.desc f g := by
  apply _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coprodCylinder_hom_ext
  · rw [_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coprodCylinderMap_inl]
    change fst A (Δ[1] : SSet.{u}) ≫ f =
      fst A (Δ[1] : SSet.{u}) ≫ (coprod.inl : A ⟶ A ⨿ C) ≫ coprod.desc f g
    rw [coprod.inl_desc]
  · rw [_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coprodCylinderMap_inr]
    change fst C (Δ[1] : SSet.{u}) ≫ g =
      fst C (Δ[1] : SSet.{u}) ≫ (coprod.inr : C ⟶ A ⨿ C) ≫ coprod.desc f g
    rw [coprod.inr_desc]

end SerrePositivity.InfinityCategories.Project.FilteredExchange
