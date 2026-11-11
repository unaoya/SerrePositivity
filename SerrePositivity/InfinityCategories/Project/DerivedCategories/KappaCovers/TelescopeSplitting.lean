module
public import SerrePositivity.DifferentialGraded.Category.Basic
public import Mathlib.CategoryTheory.Triangulated.Subcategory

/-!
概要：指定された同じ telescope 三角形の第三対象が元の retract を実現する。
方針：既存の telescope の分裂単射性と三角形の完全性で第三対象の分裂射を作る。
規約：分裂対象を任意に再選択せず、入力した cone を保持する。
使われ方：選択代表族内の実 cone による retract 代表化。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers
open CategoryTheory Limits Preadditive Pretriangulated DifferentialGraded
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  {X : C} [HasCoproduct (fun _ : ℕ => X)]

/-- 指定した telescope cone 自体が同じ冪等射を分裂する。 -/
lemma idempotentTelescope_fixedCone_splits (p : X ⟶ X) (hp : p ≫ p = p)
    {Z : C} (c : (∐ fun _ : ℕ => X) ⟶ Z)
    (h : Z ⟶ (∐ fun _ : ℕ => X)⟦(1 : ℤ)⟧)
    (hT : Triangle.mk (idempotentTelescopeMap X p) c h ∈ distTriang C) :
    ∃ (i : Z ⟶ X) (r : X ⟶ Z), i ≫ r = 𝟙 Z ∧ r ≫ i = p := by
  let T := Triangle.mk (idempotentTelescopeMap X p) c h
  have hz : h = 0 := Triangle.mor₃_eq_zero_of_mono₁ T hT
    (idempotentTelescopeMap_mono X p hp)
  have : Epi c := Triangle.epi₂ T hT hz
  let d : (∐ fun _ : ℕ => X) ⟶ X := Sigma.desc (fun _ => p)
  have hd : idempotentTelescopeMap X p ≫ d = 0 := by
    apply Sigma.hom_ext
    intro n
    simp only [idempotentTelescopeMap, idempotentTelescopeShift, d, comp_sub,
      sub_comp, Category.assoc, Sigma.ι_comp_desc, Sigma.ι_comp_desc_assoc, Category.id_comp]
    rw [hp, sub_self, comp_zero]
  obtain ⟨i, hi⟩ := Triangle.yoneda_exact₂ T hT d hd
  change d = c ≫ i at hi
  have hdc : idempotentTelescopeMap X p ≫ c = 0 := comp_distTriang_mor_zero₁₂ T hT
  have hstep (n : ℕ) : Sigma.ι (fun _ : ℕ => X) n ≫ c =
      p ≫ Sigma.ι (fun _ : ℕ => X) (n + 1) ≫ c := by
    have hn := congrArg (fun f => Sigma.ι (fun _ : ℕ => X) n ≫ f) hdc
    simpa only [idempotentTelescopeMap, idempotentTelescopeShift, comp_sub, Category.comp_id,
      sub_comp, Category.assoc, Sigma.ι_comp_desc_assoc, Category.id_comp, comp_zero,
      sub_eq_zero] using hn
  have hpc (n : ℕ) : p ≫ Sigma.ι (fun _ : ℕ => X) n ≫ c =
      Sigma.ι (fun _ : ℕ => X) n ≫ c := by
    rw [hstep n, ← Category.assoc p p, hp]
  have hconst (n : ℕ) : Sigma.ι (fun _ : ℕ => X) n ≫ c =
      Sigma.ι (fun _ : ℕ => X) 0 ≫ c := by
    induction n with
    | zero => rfl
    | succ n ih => rw [← hpc (n + 1), ← hstep n, ih]
  refine ⟨i, Sigma.ι (fun _ : ℕ => X) 0 ≫ c, ?_, ?_⟩
  · apply (cancel_epi c).1
    simp only [← Category.assoc, Category.comp_id]
    rw [← hi]
    apply Sigma.hom_ext
    intro n
    simp only [Category.assoc, d, Sigma.ι_comp_desc_assoc]
    rw [hpc 0, hconst n]
  · rw [Category.assoc, ← hi]
    exact Sigma.ι_comp_desc _ _

/-- 入力した retract と、指定した telescope cone は同型。 -/
lemma idempotentTelescope_fixedCone_iso {Y Z : C} (s : Retract Y X)
    (c : (∐ fun _ : ℕ => X) ⟶ Z)
    (h : Z ⟶ (∐ fun _ : ℕ => X)⟦(1 : ℤ)⟧)
    (hT : Triangle.mk (idempotentTelescopeMap X (s.r ≫ s.i)) c h ∈ distTriang C) :
    Nonempty (Z ≅ Y) := by
  have hp : (s.r ≫ s.i) ≫ (s.r ≫ s.i) = s.r ≫ s.i := by
    simp only [Category.assoc, s.retract_assoc]
  obtain ⟨i, r, hir, hri⟩ := idempotentTelescope_fixedCone_splits (s.r ≫ s.i) hp c h hT
  exact ⟨{
    hom := i ≫ s.r
    inv := s.i ≫ r
    hom_inv_id := by
      rw [Category.assoc, ← Category.assoc s.r, ← hri]
      simp [← Category.assoc, hir]
    inv_hom_id := by
      rw [Category.assoc, ← Category.assoc r, hri]
      simp [← Category.assoc, s.retract] }⟩

/-- 三角的対象条件の可算直和閉性から、同じ周囲圏内の retract 閉性を得る。 -/
lemma triangulatedProperty_of_retract_countable
    [HasColimitsOfShape (Discrete ℕ) C]
    (P : ObjectProperty C) [P.IsTriangulated] [P.IsClosedUnderIsomorphisms]
    (hcount : ∀ X : C, P X → P (∐ fun _ : ℕ => X)) {Y : C} (s : Retract Y X) (hX : P X) : P Y := by
  obtain ⟨Z, c, h, hT⟩ := distinguished_cocone_triangle
    (idempotentTelescopeMap X (s.r ≫ s.i))
  have hsum := hcount X hX
  have hZ : P Z := P.ext_of_isTriangulatedClosed₃ _ hT hsum hsum
  obtain ⟨e⟩ := idempotentTelescope_fixedCone_iso s c h hT
  exact P.prop_of_iso e hZ

end SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers
