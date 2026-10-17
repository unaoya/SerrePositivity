module
public import Mathlib.CategoryTheory.Localization.Construction

/-! # 局所化の生成射からのHom比較の自然性 -/
@[expose] public section
noncomputable section
universe u₁ v₁ u₂ v₂
namespace SerrePositivity.DifferentialGraded
open CategoryTheory

/-- 終域側の自然性は局所化前の射について検証すればよい。 -/
lemma localizationHom_naturality_right
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (W : MorphismProperty D) (F : C ⥤ W.Localization) (G : W.Localization ⥤ C)
    (α : ∀ X Y, (F.obj X ⟶ Y) → (X ⟶ G.obj Y))
    (h : ∀ (X : C) {Y Y' : D} (g : Y ⟶ Y') (φ : F.obj X ⟶ W.Q.obj Y),
      α X (W.Q.obj Y') (φ ≫ W.Q.map g) = α X (W.Q.obj Y) φ ≫ G.map (W.Q.map g))
    (X : C) {Y Y' : W.Localization} (g : Y ⟶ Y') (φ : F.obj X ⟶ Y) :
    α X Y' (φ ≫ g) = α X Y φ ≫ G.map g := by
  let P : MorphismProperty W.Localization := fun Y Y' g =>
    ∀ (X : C) (φ : F.obj X ⟶ Y), α X Y' (φ ≫ g) = α X Y φ ≫ G.map g
  have : P.IsStableUnderComposition := ⟨by
      intro _ _ _ f g hf hg X φ
      rw [← Category.assoc, hg, hf, G.map_comp, Category.assoc]⟩
  have hP : P = ⊤ := Localization.Construction.morphismProperty_eq_top' (W := W) P
    (fun {_ _} f => fun X φ => h X f φ) (by
      intro Y Y' e he X φ
      have ht := he X (φ ≫ e.inv)
      simp only [Category.assoc, e.inv_hom_id, Category.comp_id] at ht
      apply (cancel_mono (G.map e.hom)).mp
      rw [Category.assoc, ← G.map_comp, e.inv_hom_id, G.map_id, Category.comp_id]
      exact ht.symm)
  exact (show P g from hP ▸ trivial) X φ

/-- 始域側の自然性も局所化前の射から拡張できる。 -/
lemma localizationHom_naturality_left
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (W : MorphismProperty C) (F : W.Localization ⥤ D) (G : D ⥤ W.Localization)
    (α : ∀ X Y, (F.obj X ⟶ Y) → (X ⟶ G.obj Y))
    (h : ∀ {X X' : C} (f : X ⟶ X') (Y : D) (φ : F.obj (W.Q.obj X') ⟶ Y),
      α (W.Q.obj X) Y (F.map (W.Q.map f) ≫ φ) = W.Q.map f ≫ α (W.Q.obj X') Y φ)
    {X X' : W.Localization} (f : X ⟶ X') (Y : D) (φ : F.obj X' ⟶ Y) :
    α X Y (F.map f ≫ φ) = f ≫ α X' Y φ := by
  let P : MorphismProperty W.Localization := fun X X' f =>
    ∀ (Y : D) (φ : F.obj X' ⟶ Y), α X Y (F.map f ≫ φ) = f ≫ α X' Y φ
  have : P.IsStableUnderComposition := ⟨by
      intro _ _ _ f g hf hg Y φ
      rw [F.map_comp, Category.assoc, hf, hg, Category.assoc]⟩
  have hP : P = ⊤ := Localization.Construction.morphismProperty_eq_top' (W := W) P
    (fun {_ _} f => fun Y φ => h f Y φ) (by
      intro X X' e he Y φ
      have ht := he Y (F.map e.inv ≫ φ)
      simp only [← Category.assoc, ← F.map_comp, e.hom_inv_id, F.map_id,
        Category.id_comp] at ht
      apply (cancel_epi e.hom).mp
      rw [← Category.assoc, e.hom_inv_id, Category.id_comp]
      exact ht.symm)
  exact (show P f from hP ▸ trivial) Y φ

end SerrePositivity.DifferentialGraded
