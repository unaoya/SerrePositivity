module

public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.EssentialImage

/-! # スカラー恒等射と局所化の比較 -/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity

open CategoryTheory

variable {R S : Type*} [Ring R] [Ring S] (φ : R →+* S)
  {C : Type u₁} [Category.{v₁} C] [Preadditive C] [Linear R C]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D] [Linear S D]

/-- 指定されたスカラーが恒等射を消すという性質は同型で移せる。 -/
lemma smul_id_zero_of_iso {X Y : C} (i : X ≅ Y) (r : R) (h : r • 𝟙 X = 0) :
    r • 𝟙 Y = 0 := by
  calc
    _ = i.inv ≫ (r • 𝟙 X) ≫ i.hom := by simp
    _ = 0 := by rw [h]; simp

/-- 恒等射のスカラー倍を保つという性質は対象の同型で移せる。 -/
lemma map_smul_id_of_iso (F : C ⥤ D) {X Y : C} (i : X ≅ Y) (r : R)
    (h : F.map (r • 𝟙 X) = φ r • 𝟙 (F.obj X)) :
    F.map (r • 𝟙 Y) = φ r • 𝟙 (F.obj Y) := by
  apply (cancel_epi (F.map i.hom)).mp
  calc
    F.map i.hom ≫ F.map (r • 𝟙 Y) = F.map (r • 𝟙 X) ≫ F.map i.hom := by
      rw [← F.map_comp, ← F.map_comp]
      simp
    _ = _ := by rw [h]; simp

variable {B : Type u₃} [Category.{v₃} B] [Preadditive B] [Linear R B]

/-- 本質的全射な R 線形関手との合成上で確認したスカラーの式を降ろす。 -/
lemma map_smul_id_of_precomp (L : B ⥤ C) [L.Linear R] [L.EssSurj]
    (F : C ⥤ D) (H : B ⥤ D) (i : L ⋙ F ≅ H)
    (hH : ∀ (X : B) (r : R), H.map (r • 𝟙 X) = φ r • 𝟙 (H.obj X))
    (Y : C) (r : R) : F.map (r • 𝟙 Y) = φ r • 𝟙 (F.obj Y) := by
  obtain ⟨X, ⟨j⟩⟩ := Functor.EssSurj.mem_essImage L Y
  apply map_smul_id_of_iso φ F j r
  apply (cancel_mono (i.app X).hom).mp
  have h := i.hom.naturality (r • 𝟙 X)
  simpa only [Functor.comp_obj, Iso.app_hom, Functor.comp_map, Functor.map_smul, L.map_id, hH,
    Linear.comp_smul, Linear.smul_comp, Category.id_comp, Category.comp_id] using h

end SerrePositivity
