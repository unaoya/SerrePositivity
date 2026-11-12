module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.IntervalPullbackLift

/-!
概要：共通標的を固定した cospan の入力同型は、全 path を保つ interval 引き戻し同型を与える。
方針：元の三座標で両向きの射を持ち上げ、三座標の一意性で往復を確認する。
規約：path の全円柱を変更しない。使われ方：模型の入力 fiber の射影表示の同定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2
variable {X X' Y Y' Z : SSet.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) (f' : X' ⟶ Z) (g' : Y' ⟶ Z)
  (s : X ≅ X') (t : Y ≅ Y') (hs : s.hom ≫ f' = f) (ht : t.hom ≫ g' = g)

/-- 入力同型による、全 path 座標を保つ interval 引き戻しの比較射。 -/
def intervalPullbackInputIsoHom : intervalPullback f g ⟶ intervalPullback f' g' :=
  intervalPullbackLift f' g' (intervalPullbackPath f g)
    (intervalPullbackLeft f g ≫ s.hom) (intervalPullbackRight f g ≫ t.hom)
    (by rw [Category.assoc, hs, intervalPullbackPath_zero])
    (by rw [Category.assoc, ht, intervalPullbackPath_one])

/-- この比較射は元の path の全族を厳密に保持する。 -/
lemma intervalPullbackInputIsoHom_path :
    intervalPullbackInputIsoHom f g f' g' s t hs ht ≫ intervalPullbackPath f' g' =
      intervalPullbackPath f g := intervalPullbackLift_path _ _ _ _ _ _ _

/-- この比較射は元の左入力を指定した同型で移す。 -/
lemma intervalPullbackInputIsoHom_left :
    intervalPullbackInputIsoHom f g f' g' s t hs ht ≫ intervalPullbackLeft f' g' =
      intervalPullbackLeft f g ≫ s.hom := intervalPullbackLift_left _ _ _ _ _ _ _

/-- この比較射は元の右入力も指定した同型で移す。 -/
lemma intervalPullbackInputIsoHom_right :
    intervalPullbackInputIsoHom f g f' g' s t hs ht ≫ intervalPullbackRight f' g' =
      intervalPullbackRight f g ≫ t.hom := intervalPullbackLift_right _ _ _ _ _ _ _

/-- 入力の同じ表示同型から、全 path を厳密に保つ引き戻し同型を構成する。 -/
def intervalPullbackInputIso : intervalPullback f g ≅ intervalPullback f' g' where
  hom := intervalPullbackInputIsoHom f g f' g' s t hs ht
  inv := intervalPullbackInputIsoHom f' g' f g s.symm t.symm
    (by rw [Iso.symm_hom, ← hs, Iso.inv_hom_id_assoc])
    (by rw [Iso.symm_hom, ← ht, Iso.inv_hom_id_assoc])
  hom_inv_id := by
    apply intervalPullback_hom_ext
    · simp only [Category.assoc, intervalPullbackInputIsoHom_path, Category.id_comp]
    · rw [Category.assoc, intervalPullbackInputIsoHom_left, ← Category.assoc,
        intervalPullbackInputIsoHom_left, Iso.symm_hom, Category.assoc,
        Iso.hom_inv_id, Category.comp_id, Category.id_comp]
    · rw [Category.assoc, intervalPullbackInputIsoHom_right, ← Category.assoc,
        intervalPullbackInputIsoHom_right, Iso.symm_hom, Category.assoc,
        Iso.hom_inv_id, Category.comp_id, Category.id_comp]
  inv_hom_id := by
    apply intervalPullback_hom_ext
    · simp only [Category.assoc, intervalPullbackInputIsoHom_path, Category.id_comp]
    · rw [Category.assoc, intervalPullbackInputIsoHom_left, ← Category.assoc,
        intervalPullbackInputIsoHom_left, Iso.symm_hom, Category.assoc,
        Iso.inv_hom_id, Category.comp_id, Category.id_comp]
    · rw [Category.assoc, intervalPullbackInputIsoHom_right, ← Category.assoc,
        intervalPullbackInputIsoHom_right, Iso.symm_hom, Category.assoc,
        Iso.inv_hom_id, Category.comp_id, Category.id_comp]

end SerrePositivity.InfinityCategories.F2
