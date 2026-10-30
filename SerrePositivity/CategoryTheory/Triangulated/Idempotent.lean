module

public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.Tactic.NoncommRing
public import Mathlib.CategoryTheory.Iso
public import Mathlib.CategoryTheory.Preadditive.Biproducts

/-! # 完全三角形の冪等分裂と三成分の写像

## 概要

完全三角形の冪等な自己準同型が分裂すること、二つの成分の冪等元を第三の成分の冪等元に延長できること、三次の自己準同型の共役と両立する射影、三つの直和因子への分解の成分の公式を与える。

## 方針

冪等元の延長は三角形の公理（TR3）と冪等元の補正 `e ↦ 3e² − 2e³` 型の計算による。三成分の写像は双積の成分で書く。

## 規約

三角形の射が成分ごとに同型なら同型、は Mathlib の `Triangle.isIso_of_isIsos` を使う。

## 使われ方

KTheory の位数 3 の作用（tensor cube）、PerfectComplex の冪等元の像、Karoubi 完備化。
-/

@[expose] public noncomputable section

universe v u

section TriangleIdempotentPart

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
  have : IsIso q := Triangle.isIso_of_isIsos q inferInstance inferInstance inferInstance
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

end TriangleIdempotentPart

section TriangleIdempotentCompletionPart

namespace SerrePositivity

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

/-- 冪等性の誤差の二乗が零なら、三次多項式で冪等元に補正できる。 -/
lemma idempotent_cubic {R : Type*} [Ring R] (x : R)
    (h : (x * x - x) * (x * x - x) = 0) :
    (3 * (x * x) - 2 * (x * x * x)) * (3 * (x * x) - 2 * (x * x * x)) =
      3 * (x * x) - 2 * (x * x * x) := by
  apply sub_eq_zero.mp
  calc
    _ = (4 * (x * x) - 4 * x - 3) * ((x * x - x) * (x * x - x)) := by noncomm_ring
    _ = 0 := by rw [h, mul_zero]

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- 第一・第二成分が零の三角形自己射の第三成分は二乗零。 -/
lemma triangle_end_square_zero (T : Triangle C) (hT : T ∈ distTriang C)
    (c : T.obj₃ ⟶ T.obj₃) (hg : T.mor₂ ≫ c = 0) (hh : c ≫ T.mor₃ = 0) :
    c ≫ c = 0 := by
  obtain ⟨a, ha⟩ := T.yoneda_exact₃ hT c hg
  conv_lhs => rhs; rw [ha]
  rw [← Category.assoc, hh, zero_comp]

/-- 可換な二つの冪等元を完全三角形の第三対象の冪等元へ延長できる。 -/
theorem complete_triangle_idempotent (T : Triangle C) (hT : T ∈ distTriang C)
    (p : T.obj₁ ⟶ T.obj₁) (q : T.obj₂ ⟶ T.obj₂)
    (hp : p ≫ p = p) (hq : q ≫ q = q) (hf : T.mor₁ ≫ q = p ≫ T.mor₁) :
    ∃ r : T.obj₃ ⟶ T.obj₃, r ≫ r = r ∧ T.mor₂ ≫ r = q ≫ T.mor₂ ∧
      T.mor₃ ≫ p⟦(1 : ℤ)⟧' = r ≫ T.mor₃ := by
  obtain ⟨c, hg, hh⟩ := complete_distinguished_triangle_morphism T T hT hT p q hf
  have hc₂ : T.mor₂ ≫ c ≫ c = q ≫ T.mor₂ := by
    rw [← Category.assoc, hg, Category.assoc, hg, ← Category.assoc, hq]
  have hc₃ : T.mor₂ ≫ c ≫ c ≫ c = q ≫ T.mor₂ := by
    rw [← Category.assoc T.mor₂ c (c ≫ c), hg, Category.assoc, hc₂,
      ← Category.assoc, hq]
  have hcp₂ : (c ≫ c) ≫ T.mor₃ = T.mor₃ ≫ p⟦(1 : ℤ)⟧' := by
    rw [Category.assoc, ← hh, ← Category.assoc, ← hh, Category.assoc,
      ← Functor.map_comp, hp]
  have hcp₃ : ((c ≫ c) ≫ c) ≫ T.mor₃ = T.mor₃ ≫ p⟦(1 : ℤ)⟧' := by
    rw [Category.assoc, ← hh, ← Category.assoc, hcp₂, Category.assoc,
      ← Functor.map_comp, hp]
  have he : (c ≫ c - c) ≫ (c ≫ c - c) = 0 :=
    triangle_end_square_zero T hT _
      (by rw [Preadditive.comp_sub, hc₂, hg, sub_self])
      (by rw [Preadditive.sub_comp, hcp₂, ← hh, sub_self])
  let e : End T.obj₃ := .of c
  let r : End T.obj₃ := 3 • (e * e) - 2 • (e * e * e)
  have he' : (e * e - e) * (e * e - e) = 0 := End.ext he
  have hr' : r * r = r := by
    simpa only [r, nsmul_eq_mul, Nat.cast_ofNat] using idempotent_cubic e he'
  have hr := congrArg End.asHom hr'
  have hrdef : r.asHom = 3 • (c ≫ c) - 2 • (c ≫ c ≫ c) := rfl
  refine ⟨r.asHom, hr, ?_, ?_⟩
  · rw [hrdef]
    simp only [Preadditive.comp_sub, Preadditive.comp_nsmul, hc₂, hc₃]
    abel
  · rw [hrdef]
    rw [← Category.assoc c c c]
    simp only [Preadditive.sub_comp, Preadditive.nsmul_comp, hcp₂, hcp₃]
    abel

end SerrePositivity

end TriangleIdempotentCompletionPart

section CubicConjugationPart

namespace SerrePositivity
open CategoryTheory Category

lemma conjugate_cube {C : Type*} [Category C] {Q L : C}
    (e : Q ≅ L) (t : L ⟶ L) (ht : t ≫ t ≫ t = 𝟙 L) :
    (e.hom ≫ t ≫ e.inv) ≫ (e.hom ≫ t ≫ e.inv) ≫ (e.hom ≫ t ≫ e.inv) = 𝟙 Q := by
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  simpa only [Category.assoc, id_comp, Iso.hom_inv_id] using e.hom ≫= (ht =≫ e.inv)

lemma conjugate_projection {C : Type*} [Category C] {K Q L : C}
    (p : K ⟶ Q) (e : Q ≅ L) (g : K ⟶ L) (s : K ⟶ K) (t : L ⟶ L)
    (he : p ≫ e.hom = g) (hg : s ≫ g = g ≫ t) :
    p ≫ (e.hom ≫ t ≫ e.inv) = s ≫ p := by
  apply (cancel_mono e.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, comp_id]
  rw [← Category.assoc p e.hom, he, hg]

end SerrePositivity

end CubicConjugationPart

section ThreeComponentMapsPart

namespace SerrePositivity
open CategoryTheory Category Limits Preadditive

lemma section_sum0 {C : Type*} [Category C] [Preadditive C]
    {W K Y₀ Y₁ Y₂ : C} (p₀ : W ⟶ Y₀) (p₁ : W ⟶ Y₁) (p₂ : W ⟶ Y₂)
    (d₀ : Y₀ ⟶ K) (d₁ : Y₁ ⟶ K) (d₂ : Y₂ ⟶ K) (m : K ⟶ Y₀)
    (h₀ : d₀ ≫ m = 𝟙 _) (h₁ : d₁ ≫ m = 0) (h₂ : d₂ ≫ m = 0) :
    (p₀ ≫ d₀ + p₁ ≫ d₁ + p₂ ≫ d₂) ≫ m = p₀ := by
  rw [add_comp, add_comp, Category.assoc, Category.assoc, Category.assoc, h₀, h₁, h₂]
  simp only [comp_id, comp_zero, add_zero]

lemma section_sum1 {C : Type*} [Category C] [Preadditive C]
    {W K Y₀ Y₁ Y₂ : C} (p₀ : W ⟶ Y₀) (p₁ : W ⟶ Y₁) (p₂ : W ⟶ Y₂)
    (d₀ : Y₀ ⟶ K) (d₁ : Y₁ ⟶ K) (d₂ : Y₂ ⟶ K) (m : K ⟶ Y₁)
    (h₀ : d₀ ≫ m = 0) (h₁ : d₁ ≫ m = 𝟙 _) (h₂ : d₂ ≫ m = 0) :
    (p₀ ≫ d₀ + p₁ ≫ d₁ + p₂ ≫ d₂) ≫ m = p₁ := by
  rw [add_comp, add_comp, Category.assoc, Category.assoc, Category.assoc, h₀, h₁, h₂]
  simp only [comp_id, comp_zero, zero_add, add_zero]

lemma section_sum2 {C : Type*} [Category C] [Preadditive C]
    {W K Y₀ Y₁ Y₂ : C} (p₀ : W ⟶ Y₀) (p₁ : W ⟶ Y₁) (p₂ : W ⟶ Y₂)
    (d₀ : Y₀ ⟶ K) (d₁ : Y₁ ⟶ K) (d₂ : Y₂ ⟶ K) (m : K ⟶ Y₂)
    (h₀ : d₀ ≫ m = 0) (h₁ : d₁ ≫ m = 0) (h₂ : d₂ ≫ m = 𝟙 _) :
    (p₀ ≫ d₀ + p₁ ≫ d₁ + p₂ ≫ d₂) ≫ m = p₂ := by
  rw [add_comp, add_comp, Category.assoc, Category.assoc, Category.assoc, h₀, h₁, h₂]
  simp only [comp_id, comp_zero, zero_add, add_zero]

lemma three_components_rotation {C : Type*} [Category C] [HasZeroMorphisms C]
    [HasBinaryBiproducts C] {K U₀ U₁ U₂ : C} (τ : K ⟶ K)
    (m₀ : K ⟶ U₀) (m₁ : K ⟶ U₁) (m₂ : K ⟶ U₂)
    (r₀ : U₀ ⟶ U₁) (r₁ : U₁ ⟶ U₂) (r₂ : U₂ ⟶ U₀)
    (h₀ : τ ≫ m₀ = m₂ ≫ r₂) (h₁ : τ ≫ m₁ = m₀ ≫ r₀)
    (h₂ : τ ≫ m₂ = m₁ ≫ r₁) :
    τ ≫ biprod.lift m₀ (biprod.lift m₁ m₂) =
      biprod.lift m₀ (biprod.lift m₁ m₂) ≫
        biprod.lift (biprod.snd ≫ biprod.snd ≫ r₂)
          (biprod.lift (biprod.fst ≫ r₀) (biprod.snd ≫ biprod.fst ≫ r₁)) := by
  apply biprod.hom_ext
  · simp only [Category.assoc, biprod.lift_fst, biprod.lift_snd_assoc, h₀]
  · apply biprod.hom_ext
    · simp only [Category.assoc, biprod.lift_fst, biprod.lift_fst_assoc,
        biprod.lift_snd, h₁]
    · simp only [Category.assoc, biprod.lift_fst_assoc,
        biprod.lift_snd, biprod.lift_snd_assoc, h₂]

end SerrePositivity

end ThreeComponentMapsPart
