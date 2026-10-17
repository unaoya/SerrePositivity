module
public import SerrePositivity.DifferentialGraded.Morita.CriterionDerivedHomCoproducts
public import Mathlib.CategoryTheory.Triangulated.Subcategory

/-! # Hom比較の終域変数における同型不変性と錐閉性

二つの実際のHom完全列を追う。右随伴・unit/counitは使わない。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory Limits Preadditive Pretriangulated
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (T : DerivedModuleCategory A D ⥤ DerivedModuleCategory A E)

/-- 終域の同型に沿ってHom比較の全単射性を運ぶ。 -/
lemma criterionDerivedHom_target_iso (X : DerivedModuleCategory A D)
    {Y Z : DerivedModuleCategory A D} (e : Y ≅ Z)
    (hZ : Function.Bijective (fun f : X ⟶ Z => T.map f)) :
    Function.Bijective (fun f : X ⟶ Y => T.map f) := by
  constructor
  · intro f g h
    change T.map f = T.map g at h
    apply (cancel_mono e.hom).1
    apply hZ.1
    change T.map (f ≫ e.hom) = T.map (g ≫ e.hom)
    rw [T.map_comp, T.map_comp, h]
  · intro f
    obtain ⟨g, hg⟩ := hZ.2 (f ≫ T.map e.hom)
    change T.map g = f ≫ T.map e.hom at hg
    refine ⟨g ≫ e.inv, ?_⟩
    change T.map (g ≫ e.inv) = f
    rw [T.map_comp, hg, Category.assoc, ← T.map_comp, e.hom_inv_id,
      T.map_id, Category.comp_id]

variable [T.CommShift ℤ] [T.IsTriangulated]

/-- 三角形の最初の二頂点とそのshiftでの比較から、第三頂点での全単射性を得る。 -/
lemma criterionDerivedHom_target_triangle
    (X : DerivedModuleCategory A D) (Δ : Triangle (DerivedModuleCategory A D))
    (hΔ : Δ ∈ distTriang (DerivedModuleCategory A D))
    (h1 : Function.Bijective (fun f : X ⟶ Δ.obj₁ => T.map f))
    (h2 : Function.Bijective (fun f : X ⟶ Δ.obj₂ => T.map f))
    (h1s : Function.Bijective (fun f : X ⟶ Δ.obj₁⟦(1 : ℤ)⟧ => T.map f))
    (h2s : Function.Bijective (fun f : X ⟶ Δ.obj₂⟦(1 : ℤ)⟧ => T.map f)) :
    Function.Bijective (fun f : X ⟶ Δ.obj₃ => T.map f) := by
  have hk (f : X ⟶ Δ.obj₃) (hf : T.map f = 0) : f = 0 := by
    have hz : f ≫ Δ.mor₃ = 0 := by
      apply h1s.1
      change T.map (f ≫ Δ.mor₃) = T.map 0
      rw [T.map_comp, hf, zero_comp, T.map_zero]
    obtain ⟨g, hg⟩ := Δ.coyoneda_exact₃ hΔ f hz
    have hzg : T.map g ≫ T.map Δ.mor₂ = 0 := by
      rw [← T.map_comp, ← hg, hf]
    obtain ⟨c, hc⟩ := (T.mapTriangle.obj Δ).coyoneda_exact₂
      (T.map_distinguished Δ hΔ) (T.map g) hzg
    obtain ⟨a, ha⟩ := h1.2 c
    change T.map a = c at ha
    have hga : g = a ≫ Δ.mor₁ := by
      apply h2.1
      change T.map g = T.map (a ≫ Δ.mor₁)
      rw [T.map_comp, ha]
      exact hc
    rw [hg, hga, Category.assoc, comp_distTriang_mor_zero₁₂ Δ hΔ, comp_zero]
  constructor
  · intro f g h
    apply sub_eq_zero.mp
    apply hk (f - g)
    change T.map f = T.map g at h
    rw [T.map_sub, h, sub_self]
  · intro f
    obtain ⟨a, ha⟩ := h1s.2 (f ≫ T.map Δ.mor₃)
    change T.map a = f ≫ T.map Δ.mor₃ at ha
    have hza : a ≫ Δ.mor₁⟦(1 : ℤ)⟧' = 0 := by
      apply h2s.1
      change T.map (a ≫ Δ.mor₁⟦(1 : ℤ)⟧') = T.map 0
      rw [T.map_comp, ha, Category.assoc, ← T.map_comp,
        comp_distTriang_mor_zero₃₁ Δ hΔ, T.map_zero, comp_zero, T.map_zero]
    obtain ⟨b, hb⟩ := Δ.coyoneda_exact₁ hΔ a hza
    have hdiff : (f - T.map b) ≫ (T.mapTriangle.obj Δ).mor₃ = 0 := by
      change (f - T.map b) ≫
        (T.map Δ.mor₃ ≫ (T.commShiftIso (1 : ℤ)).hom.app Δ.obj₁) = 0
      rw [← Category.assoc, sub_comp, ← T.map_comp, ← hb, ha, sub_self, zero_comp]
    obtain ⟨c, hc⟩ := (T.mapTriangle.obj Δ).coyoneda_exact₃
      (T.map_distinguished Δ hΔ) (f - T.map b) hdiff
    obtain ⟨d, hd⟩ := h2.2 c
    change T.map d = c at hd
    refine ⟨b + d ≫ Δ.mor₂, ?_⟩
    change T.map (b + d ≫ Δ.mor₂) = f
    rw [T.map_add, T.map_comp, hd]
    change f - T.map b = c ≫ T.map Δ.mor₂ at hc
    rw [← hc]
    exact add_sub_cancel _ _

/-- 零対象を終域に持つHom比較は全単射。 -/
lemma criterionDerivedHom_target_isZero (X : DerivedModuleCategory A D)
    {Y : DerivedModuleCategory A D} (hY : IsZero Y) :
    Function.Bijective (fun f : X ⟶ Y => T.map f) := by
  constructor
  · intro f g _
    exact hY.eq_of_tgt f g
  · intro f
    exact ⟨0, (T.map_isZero hY).eq_of_tgt _ _⟩

end SerrePositivity.DifferentialGraded.Morita
