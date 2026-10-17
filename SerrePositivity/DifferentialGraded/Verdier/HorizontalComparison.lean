module
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.NatIso

/-! # 比較正方形の横貼合せと同型による経路の輸送 -/
@[expose] public section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory CategoryTheory.Functor

section Horizontal
variable {C₀ C₁ C₂ V₀ V₁ V₂ : Type*}
  [Category* C₀] [Category* C₁] [Category* C₂]
  [Category* V₀] [Category* V₁] [Category* V₂]
  (L₀ : C₀ ⥤ V₀) (L₁ : C₁ ⥤ V₁) (L₂ : C₂ ⥤ V₂)
  {F F' : C₀ ⥤ C₁} {G G' : C₁ ⥤ C₂}
  {Fbar Fbar' : V₀ ⥤ V₁} {Gbar Gbar' : V₁ ⥤ V₂}
  (a : L₀ ⋙ Fbar ≅ F ⋙ L₁) (a' : L₀ ⋙ Fbar' ≅ F' ⋙ L₁)
  (b : L₁ ⋙ Gbar ≅ G ⋙ L₂) (b' : L₁ ⋙ Gbar' ≅ G' ⋙ L₂)
  (f : F ⟶ F') (g : G ⟶ G') (fbar : Fbar ⟶ Fbar') (gbar : Gbar ⟶ Gbar')

/-- 二つの比較正方形を横に貼り合わせた同型。 -/
def horizontalComparison : L₀ ⋙ (Fbar ⋙ Gbar) ≅ (F ⋙ G) ⋙ L₂ :=
  (associator _ _ _).symm ≪≫ isoWhiskerRight a Gbar ≪≫ associator _ _ _ ≪≫
    isoWhiskerLeft F b ≪≫ (associator _ _ _).symm

/-- 各比較が自然なら、その実際の横貼合せも水平合成に関して自然。 -/
lemma horizontalComparison_naturality
    (ha : whiskerLeft L₀ fbar ≫ a'.hom = a.hom ≫ whiskerRight f L₁)
    (hb : whiskerLeft L₁ gbar ≫ b'.hom = b.hom ≫ whiskerRight g L₂) :
    whiskerLeft L₀ (NatTrans.hcomp fbar gbar) ≫
        (horizontalComparison L₀ L₁ L₂ a' b').hom =
      (horizontalComparison L₀ L₁ L₂ a b).hom ≫ whiskerRight (NatTrans.hcomp f g) L₂ := by
  apply NatTrans.ext
  funext X
  have hax := NatTrans.congr_app ha X
  have hbx := NatTrans.congr_app hb (F.obj X)
  simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app] at hax hbx
  have hn := b'.hom.naturality (f.app X)
  simp only [Functor.comp_map] at hn
  have hg := gbar.naturality (a.hom.app X)
  simp only [horizontalComparison, Iso.trans_hom, Iso.symm_hom, isoWhiskerRight_hom,
    isoWhiskerLeft_hom, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
    associator_inv_app, associator_hom_app, NatTrans.hcomp_app, Category.id_comp,
    Category.comp_id, Category.assoc]
  rw [← Gbar'.map_comp_assoc, hax, Gbar'.map_comp, Category.assoc,
    hn, ← reassoc_of% hg, reassoc_of% hbx, ← L₂.map_comp]
end Horizontal

section Transport
variable {C : Type*} [Category* C]
  {X X' Y Y' A A' B B' : C}
  (a : X ≅ A) (a' : X' ≅ A') (b : Y ≅ B) (b' : Y' ≅ B')
  (e : A ≅ B) (e' : A' ≅ B') (fbar : X ⟶ X') (gbar : Y ⟶ Y')
  (f : A ⟶ A') (g : B ⟶ B')

/-- 元の比較と両側の表示変更が自然なら、輸送した比較も同じ射に自然。 -/
lemma transportedComparison_naturality
    (ha : fbar ≫ a'.hom = a.hom ≫ f)
    (hb : gbar ≫ b'.hom = b.hom ≫ g) (he : f ≫ e'.hom = e.hom ≫ g) :
    fbar ≫ a'.hom ≫ e'.hom ≫ b'.inv = a.hom ≫ e.hom ≫ b.inv ≫ gbar := by
  apply (cancel_mono b'.hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← Category.assoc, ha]
  simp only [Category.assoc]
  rw [he, hb]
  simp only [← Category.assoc, Iso.inv_hom_id, Category.comp_id]
end Transport
end SerrePositivity.DifferentialGraded
