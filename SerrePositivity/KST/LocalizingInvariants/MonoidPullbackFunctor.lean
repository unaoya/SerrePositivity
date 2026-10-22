module

public import SerrePositivity.KST.LocalizingInvariants.MonoidPullbackUniversal
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Cospan

/-!
概要：元のモノイド対象の通常 pullback を、元の cospan 図式上の厳密な関手にする。
方針：元の二射影の普遍性で射を構成し、二成分で関手則を確認する。
規約：tensor の極限保存は不要。使われ方：底を揃える実代数の pro 逆。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory Limits WalkingCospan WalkingCospan.Hom
namespace SerrePositivity.KST.LocalizingInvariants.MonoidPullback
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [HasPullbacks C]

def diagramObject (D : WalkingCospan ⥤ Mon C) : Mon C := obj (D.map inl) (D.map inr)

def diagramMap {D E : WalkingCospan ⥤ Mon C} (α : D ⟶ E) :
    diagramObject D ⟶ diagramObject E :=
  lift (E.map inl) (E.map inr)
    (fst (D.map inl) (D.map inr) ≫ α.app .left)
    (snd (D.map inl) (D.map inr) ≫ α.app .right) (by
      rw [Category.assoc, ← α.naturality inl, ← Category.assoc, condition,
        Category.assoc, α.naturality inr, ← Category.assoc])

lemma diagramMap_fst {D E : WalkingCospan ⥤ Mon C} (α : D ⟶ E) :
    diagramMap α ≫ fst (E.map inl) (E.map inr) =
      fst (D.map inl) (D.map inr) ≫ α.app .left := lift_fst _ _ _ _ _

lemma diagramMap_snd {D E : WalkingCospan ⥤ Mon C} (α : D ⟶ E) :
    diagramMap α ≫ snd (E.map inl) (E.map inr) =
      snd (D.map inl) (D.map inr) ≫ α.app .right := lift_snd _ _ _ _ _

lemma diagramMap_id (D : WalkingCospan ⥤ Mon C) : diagramMap (𝟙 D) = 𝟙 (diagramObject D) := by
  apply hom_ext (D.map inl) (D.map inr)
  · rw [diagramMap_fst]; simp
  · rw [diagramMap_snd]; simp

lemma diagramMap_comp {D E F : WalkingCospan ⥤ Mon C} (α : D ⟶ E) (β : E ⟶ F) :
    diagramMap (α ≫ β) = diagramMap α ≫ diagramMap β := by
  apply hom_ext (F.map inl) (F.map inr)
  · rw [diagramMap_fst, Category.assoc, diagramMap_fst, ← Category.assoc, diagramMap_fst]
    exact (Category.assoc _ _ _).symm
  · rw [diagramMap_snd, Category.assoc, diagramMap_snd, ← Category.assoc, diagramMap_snd]
    exact (Category.assoc _ _ _).symm

def diagramFunctor : (WalkingCospan ⥤ Mon C) ⥤ Mon C where
  obj := diagramObject
  map := diagramMap
  map_id := diagramMap_id
  map_comp := diagramMap_comp

end SerrePositivity.KST.LocalizingInvariants.MonoidPullback
