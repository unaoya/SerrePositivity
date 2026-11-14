module
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.CoproductInternalHom

/-!
概要：直和の二つの指定円柱を一つの円柱へ貼る。
方針：右の区間直積が直和を保つ比較同型を使う。
規約：時間は右因子、両枝の全円柱を厳密に保持。
使われ方：元の二入力の輸送を標的の境界の指定輸送としてまとめる。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 概要：二つの円柱の直和上の貼り合わせ。
方針：右直積の直和比較の逆を使う。
規約：全時刻。使われ方：境界の輸送円柱。 -/
def coprodCylinderMap {A C X : SSet.{u}}
    (H : A ⊗ (Δ[1] : SSet.{u}) ⟶ X) (G : C ⊗ (Δ[1] : SSet.{u}) ⟶ X) :
    (A ⨿ C) ⊗ (Δ[1] : SSet.{u}) ⟶ X :=
  (PreservesColimitPair.iso (tensorRight (Δ[1] : SSet.{u})) A C).inv ≫ coprod.desc H G

/-- 概要：左枝の制限は元の全円柱。
方針：直和比較の左脚を計算。規約：厳密な一致。使われ方：第一入力の輸送保持。 -/
lemma coprodCylinderMap_inl {A C X : SSet.{u}}
    (H : A ⊗ (Δ[1] : SSet.{u}) ⟶ X) (G : C ⊗ (Δ[1] : SSet.{u}) ⟶ X) :
    ((coprod.inl : A ⟶ A ⨿ C) ▷ (Δ[1] : SSet.{u})) ≫ coprodCylinderMap H G = H := by
  rw [coprodCylinderMap, ← _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.tensorCoprod_inl, Category.assoc,
    Iso.hom_inv_id_assoc, coprod.inl_desc]

/-- 概要：右枝の制限は元の全円柱。
方針：直和比較の右脚を計算。規約：厳密な一致。使われ方：第二入力の輸送保持。 -/
lemma coprodCylinderMap_inr {A C X : SSet.{u}}
    (H : A ⊗ (Δ[1] : SSet.{u}) ⟶ X) (G : C ⊗ (Δ[1] : SSet.{u}) ⟶ X) :
    ((coprod.inr : C ⟶ A ⨿ C) ▷ (Δ[1] : SSet.{u})) ≫ coprodCylinderMap H G = G := by
  rw [coprodCylinderMap, ← _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.tensorCoprod_inr, Category.assoc,
    Iso.hom_inv_id_assoc, coprod.inr_desc]

/-- 概要：貼り合わせの始点は元の二つの始点の組。
方針：両枝で始点包含の自然性を使う。
規約：元の二入力。使われ方：指定境界輸送の始点の一致。 -/
lemma coprodCylinderMap_zero {A C X : SSet.{u}}
    (H : A ⊗ (Δ[1] : SSet.{u}) ⟶ X) (G : C ⊗ (Δ[1] : SSet.{u}) ⟶ X) :
    SSet.ι₀ ≫ coprodCylinderMap H G = coprod.desc (SSet.ι₀ ≫ H) (SSet.ι₀ ≫ G) := by
  apply coprod.hom_ext
  · rw [← Category.assoc, ← SSet.ι₀_comp, Category.assoc, coprodCylinderMap_inl, coprod.inl_desc]
  · rw [← Category.assoc, ← SSet.ι₀_comp, Category.assoc, coprodCylinderMap_inr, coprod.inr_desc]

/-- 概要：貼り合わせの終点は元の二つの終点の組。
方針：両枝で終点包含の自然性を使う。
規約：元の二入力。使われ方：指定境界輸送の終点の一致。 -/
lemma coprodCylinderMap_one {A C X : SSet.{u}}
    (H : A ⊗ (Δ[1] : SSet.{u}) ⟶ X) (G : C ⊗ (Δ[1] : SSet.{u}) ⟶ X) :
    SSet.ι₁ ≫ coprodCylinderMap H G = coprod.desc (SSet.ι₁ ≫ H) (SSet.ι₁ ≫ G) := by
  apply coprod.hom_ext
  · rw [← Category.assoc, ← SSet.ι₁_comp, Category.assoc, coprodCylinderMap_inl, coprod.inl_desc]
  · rw [← Category.assoc, ← SSet.ι₁_comp, Category.assoc, coprodCylinderMap_inr, coprod.inr_desc]

/-- 概要：直和の円柱への射は二つの枝への制限で決まる。
方針：右直積の直和比較の同型を消去する。
規約：全時刻。使われ方：指定した底の全円柱の一致。 -/
lemma coprodCylinder_hom_ext {A C X : SSet.{u}}
    {H G : (A ⨿ C) ⊗ (Δ[1] : SSet.{u}) ⟶ X}
    (h : ((coprod.inl : A ⟶ A ⨿ C) ▷ (Δ[1] : SSet.{u})) ≫ H =
      ((coprod.inl : A ⟶ A ⨿ C) ▷ (Δ[1] : SSet.{u})) ≫ G)
    (k : ((coprod.inr : C ⟶ A ⨿ C) ▷ (Δ[1] : SSet.{u})) ≫ H =
      ((coprod.inr : C ⟶ A ⨿ C) ▷ (Δ[1] : SSet.{u})) ≫ G) : H = G := by
  apply (cancel_epi (PreservesColimitPair.iso (tensorRight (Δ[1] : SSet.{u})) A C).hom).1
  apply coprod.hom_ext
  · rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.tensorCoprod_inl, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.tensorCoprod_inl]
    exact h
  · rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.tensorCoprod_inr, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.tensorCoprod_inr]
    exact k

/-- 概要：二円柱の貼り合わせは標的への後合成と交換する。
方針：両枝へ制限して比較する。
規約：全円柱の厳密な式。使われ方：元の境界輸送を Kan 置換へ写す。 -/
lemma coprodCylinderMap_comp {A C X Y : SSet.{u}}
    (H : A ⊗ (Δ[1] : SSet.{u}) ⟶ X) (G : C ⊗ (Δ[1] : SSet.{u}) ⟶ X) (q : X ⟶ Y) :
    coprodCylinderMap H G ≫ q = coprodCylinderMap (H ≫ q) (G ≫ q) := by
  apply coprodCylinder_hom_ext
  · rw [← Category.assoc, coprodCylinderMap_inl, coprodCylinderMap_inl]
  · rw [← Category.assoc, coprodCylinderMap_inr, coprodCylinderMap_inr]

end SerrePositivity.InfinityCategories.Project.FilteredExchange
