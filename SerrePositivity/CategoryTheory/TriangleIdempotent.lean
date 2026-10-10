module

public import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-!
# 完全三角形の冪等分裂

三角形の両端で零になる自己射の中央成分は平方零である。
この事実を使い、両端で与えられた冪等分裂を中央へ延長する。
Karoubi 包絡に三角構造を入れることを前提としない。
-/

@[expose] public section

universe v u

namespace SerrePositivity

open CategoryTheory CategoryTheory.Category CategoryTheory.Preadditive
open CategoryTheory.Limits CategoryTheory.Pretriangulated

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- 完全三角形の両端で零となる自己射の中央成分は平方零である。 -/
lemma triangle_middle_sq_zero (T : Triangle C) (hT : T ∈ distTriang C)
    (p : T ⟶ T) (h₁ : p.hom₁ = 0) (h₃ : p.hom₃ = 0) :
    p.hom₂ ≫ p.hom₂ = 0 := by
  have hleft : T.mor₁ ≫ p.hom₂ = 0 := by rw [p.comm₁, h₁, zero_comp]
  have hright : p.hom₂ ≫ T.mor₂ = 0 := by rw [← p.comm₂, h₃, comp_zero]
  obtain ⟨f, hf⟩ := Triangle.coyoneda_exact₂ T hT p.hom₂ hright
  calc
    p.hom₂ ≫ p.hom₂ = f ≫ T.mor₁ ≫ p.hom₂ := by rw [hf, assoc]
    _ = 0 := by rw [hleft, comp_zero]

/-- 完全三角形の両端で零となる冪等自己射は零である。 -/
lemma triangle_idempotent_eq_zero (T : Triangle C) (hT : T ∈ distTriang C)
    (p : T ⟶ T) (hp : p ≫ p = p) (h₁ : p.hom₁ = 0) (h₃ : p.hom₃ = 0) :
    p = 0 := by
  ext
  · exact h₁
  · have h := congrArg (fun f : T ⟶ T ↦ f.hom₂) hp
    exact h.symm.trans (triangle_middle_sq_zero T hT p h₁ h₃)
  · exact h₃

omit [Preadditive C] [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] in
/-- 三角形の全成分が同型ならば三角形の射自身も同型である。 -/
lemma triangle_isIso_of_components {T U : Triangle C} (f : T ⟶ U)
    [IsIso f.hom₁] [IsIso f.hom₂] [IsIso f.hom₃] : IsIso f := by
  let e := Triangle.isoMk T U (asIso f.hom₁) (asIso f.hom₂) (asIso f.hom₃)
    f.comm₁ f.comm₂ f.comm₃
  have he : e.hom = f := by ext <;> rfl
  rw [← he]
  infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- 完全三角形の冪等自己射は、両端の成分が分裂すれば完全三角形を像として分裂する。 -/
lemma distinguished_triangle_idempotent_splits
    (T : Triangle C) (hT : T ∈ distTriang C) (p : T ⟶ T) (hp : p ≫ p = p)
    (A B : C) (i₁ : A ⟶ T.obj₁) (r₁ : T.obj₁ ⟶ A)
    (i₃ : B ⟶ T.obj₃) (r₃ : T.obj₃ ⟶ B)
    (hi₁ : i₁ ≫ r₁ = 𝟙 A) (hr₁ : r₁ ≫ i₁ = p.hom₁)
    (hi₃ : i₃ ≫ r₃ = 𝟙 B) (hr₃ : r₃ ≫ i₃ = p.hom₃) :
    ∃ (U : Triangle C), U ∈ distTriang C ∧
      ∃ (i : U ⟶ T) (r : T ⟶ U), i ≫ r = 𝟙 U ∧ r ≫ i = p := by
  let δ := i₃ ≫ T.mor₃ ≫ r₁⟦(1 : ℤ)⟧'
  obtain ⟨Y, f, g, hU⟩ := distinguished_cocone_triangle₂ δ
  let U := Triangle.mk f g δ
  have hcommi : U.mor₃ ≫ i₁⟦(1 : ℤ)⟧' = i₃ ≫ T.mor₃ := by
    dsimp [U, δ]
    rw [assoc, assoc, ← Functor.map_comp, hr₁, p.comm₃]
    rw [← assoc, ← hr₃, ← assoc, hi₃, Category.id_comp]
  have hcommr : T.mor₃ ≫ r₁⟦(1 : ℤ)⟧' = r₃ ≫ U.mor₃ := by
    dsimp [U, δ]
    rw [← assoc r₃, hr₃, ← p.comm₃_assoc, ← Functor.map_comp,
      ← hr₁, assoc, hi₁, Category.comp_id]
  obtain ⟨a₂, ha₁, ha₂⟩ := complete_distinguished_triangle_morphism₂ U T hU hT
    i₁ i₃ hcommi
  obtain ⟨b₂, hb₁, hb₂⟩ := complete_distinguished_triangle_morphism₂ T U hT hU
    r₁ r₃ hcommr
  let a : U ⟶ T := ⟨i₁, a₂, i₃, ha₁, ha₂, hcommi⟩
  let b : T ⟶ U := ⟨r₁, b₂, r₃, hb₁, hb₂, hcommr⟩
  let i := a ≫ p
  let r := p ≫ b
  have hip : i ≫ p = i := by dsimp only [i]; rw [assoc, hp]
  have hpr : p ≫ r = r := by dsimp only [r]; rw [← assoc, hp]
  have hi : i.hom₁ = i₁ := by dsimp [i, a]; rw [← hr₁, ← assoc, hi₁]; exact Category.id_comp i₁
  have hr : r.hom₁ = r₁ := by dsimp [r, b]; rw [← hr₁, assoc, hi₁, Category.comp_id]
  have hi' : i.hom₃ = i₃ := by dsimp [i, a]; rw [← hr₃, ← assoc, hi₃]; exact Category.id_comp i₃
  have hr' : r.hom₃ = r₃ := by dsimp [r, b]; rw [← hr₃, assoc, hi₃, Category.comp_id]
  let q := i ≫ r
  have hq₁ : q.hom₁ = 𝟙 A := by change i.hom₁ ≫ r.hom₁ = _; rw [hi, hr, hi₁]
  have hq₃ : q.hom₃ = 𝟙 B := by change i.hom₃ ≫ r.hom₃ = _; rw [hi', hr', hi₃]
  have : IsIso q.hom₁ := by rw [hq₁]; exact inferInstanceAs (IsIso (𝟙 A))
  have : IsIso q.hom₃ := by rw [hq₃]; exact inferInstanceAs (IsIso (𝟙 B))
  have : IsIso q.hom₂ := isIso₂_of_isIso₁₃ q hU hU inferInstance inferInstance
  have : IsIso q := triangle_isIso_of_components q
  let r' := r ≫ inv q
  have hir : i ≫ r' = 𝟙 U := by dsimp only [r']; rw [← assoc]; exact IsIso.hom_inv_id q
  have hpr' : p ≫ r' = r' := by dsimp only [r']; rw [← assoc, hpr]
  have hpe : p ≫ (r' ≫ i) = r' ≫ i := by rw [← assoc, hpr']
  have hep : (r' ≫ i) ≫ p = r' ≫ i := by rw [assoc, hip]
  have hee : (r' ≫ i) ≫ (r' ≫ i) = r' ≫ i := by
    rw [assoc, ← assoc i r' i, hir, Category.id_comp]
  have he : (p - r' ≫ i) ≫ (p - r' ≫ i) = p - r' ≫ i := by
    simp only [comp_sub, sub_comp, hp, hpe, hep, hee, sub_self, sub_zero]
  have hzero : p - r' ≫ i = 0 := by
    apply triangle_idempotent_eq_zero T hT _ he
    · change p.hom₁ - (r.hom₁ ≫ (inv q).hom₁) ≫ i.hom₁ = 0
      have hqi : (inv q).hom₁ = 𝟙 A := by
        have h := congrArg (fun z : U ⟶ U ↦ z.hom₁) (IsIso.hom_inv_id q)
        change q.hom₁ ≫ (inv q).hom₁ = 𝟙 A at h
        rw [hq₁] at h
        exact (Category.id_comp ((inv q).hom₁)).symm.trans h
      rw [hi, hr, hqi, Category.comp_id r₁, hr₁, sub_self]
    · change p.hom₃ - (r.hom₃ ≫ (inv q).hom₃) ≫ i.hom₃ = 0
      have hqi : (inv q).hom₃ = 𝟙 B := by
        have h := congrArg (fun z : U ⟶ U ↦ z.hom₃) (IsIso.hom_inv_id q)
        change q.hom₃ ≫ (inv q).hom₃ = 𝟙 B at h
        rw [hq₃] at h
        exact (Category.id_comp ((inv q).hom₃)).symm.trans h
      rw [hi', hr', hqi, Category.comp_id r₃, hr₃, sub_self]
  exact ⟨U, hU, i, r', hir, (sub_eq_zero.mp hzero).symm⟩

end SerrePositivity
