module

public import SerrePositivity.CategoryTheory.TStructure.Basic
public import SerrePositivity.CategoryTheory.Triangulated.Idempotent
public import Mathlib.CategoryTheory.Triangulated.TStructure.Heart
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT

/-! # 有界 t 構造の冪等完備性と heart からの生成

## 概要

有界 t 構造をもつ三角圏の有界部分圏が冪等完備であること、対象が heart の対象から有限の Postnikov 塔で生成されることを示す。

## 方針

冪等元は切り詰めで次数ごとに分け、heart の冪等完備性に帰着する。生成は次数の幅についての帰納法。

## 規約

`TStructure/Basic` の上に置く。

## 使われ方

局所化上の t 構造（`TStructure/Localization`）、Serre 商の導来圏（`Derived`）。
-/

@[expose] public noncomputable section

universe v u

section BoundedTStructureIdempotentPart

namespace SerrePositivity

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated CategoryTheory.Idempotents

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C] (t : TStructure C)

set_option backward.defeqAttrib.useBackward true in
/-- 有限な次数幅をもつ対象の冪等元は分裂する。 -/
lemma finiteAmplitude_idempotent_splits (w : ℕ) (X : C) (a : ℤ)
    [t.IsGE X a] [t.IsLE X (a + w)] (p : X ⟶ X) (hp : p ≫ p = p) :
    ∃ (Y : C) (i : Y ⟶ X) (r : X ⟶ Y), i ≫ r = 𝟙 Y ∧ r ≫ i = p := by
  induction w generalizing X a with
  | zero =>
    have : t.IsLE X a := by simpa using (inferInstance : t.IsLE X (a + (0 : ℕ)))
    obtain ⟨Y, _, _, i, r, hir, hri⟩ := pure_idempotent_splits t X a p hp
    exact ⟨Y, i, r, hir, hri⟩
  | succ w ih =>
    let n : ℤ := a + w
    let F := t.triangleLEGE n (n + 1) rfl
    let T := F.obj X
    let e := F.map p
    have he : e ≫ e = e := by dsimp only [e]; rw [← Functor.map_comp, hp]
    have hT : T ∈ distTriang C := t.triangleLEGE_distinguished n (n + 1) rfl X
    have hle : t.IsLE X (n + 1) := by
      convert (inferInstance : t.IsLE X (a + (w + 1 : ℕ))) using 1
      dsimp [n]
      omega
    have : t.IsGE T.obj₁ a := by dsimp [T, F]; infer_instance
    have : t.IsLE T.obj₁ (a + w) := by dsimp [T, F, n]; infer_instance
    have : t.IsGE T.obj₃ (n + 1) := by dsimp [T, F]; infer_instance
    have : t.IsLE T.obj₃ (n + 1) := by dsimp [T, F]; infer_instance
    obtain ⟨A, i₁, r₁, hi₁, hr₁⟩ := ih T.obj₁ a e.hom₁
      (congrArg (fun f : T ⟶ T ↦ f.hom₁) he)
    obtain ⟨B, _, _, i₃, r₃, hi₃, hr₃⟩ := pure_idempotent_splits t T.obj₃ (n + 1)
      e.hom₃ (congrArg (fun f : T ⟶ T ↦ f.hom₃) he)
    obtain ⟨U, _, i, r, hir, hri⟩ := distinguished_triangle_idempotent_splits
      T hT e he A B i₁ r₁ i₃ r₃ hi₁ hr₁ hi₃ hr₃
    exact ⟨U.obj₂, i.hom₂, r.hom₂,
      congrArg (fun f : U ⟶ U ↦ f.hom₂) hir,
      congrArg (fun f : T ⟶ T ↦ f.hom₂) hri⟩

/-- 上下に有界な対象の冪等元は、元の次数範囲を保った対象を像として分裂する。 -/
lemma bounded_idempotent_splits (X : C) (a b : ℤ) [t.IsGE X a] [t.IsLE X b]
    (p : X ⟶ X) (hp : p ≫ p = p) :
    ∃ (Y : C), t.IsGE Y a ∧ t.IsLE Y b ∧
      ∃ (i : Y ⟶ X) (r : X ⟶ Y), i ≫ r = 𝟙 Y ∧ r ≫ i = p := by
  have : t.IsLE X (a + (b - a).toNat) := t.isLE_of_le X b _ (by omega)
  obtain ⟨Y, i, r, hir, hri⟩ := finiteAmplitude_idempotent_splits t (b - a).toNat X a p hp
  let R : Retract Y X := ⟨i, r, hir⟩
  exact ⟨Y, tStructure_isGE_of_retract t R a, tStructure_isLE_of_retract t R b,
    i, r, hir, hri⟩

/-- 全対象が t 構造に関して有界ならば、その三角圏は冪等完備である。 -/
lemma isIdempotentComplete_of_bounded_tStructure (hb : ∀ X : C, t.bounded X) :
    IsIdempotentComplete C := by
  constructor
  intro X p hp
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hb X
  obtain ⟨Y, _, _, i, r, hir, hri⟩ := bounded_idempotent_splits t X a b p hp
  exact ⟨Y, i, r, hir, hri⟩

/-- 周囲の圏全体の有界性を仮定せず、有界対象の充満部分圏は冪等完備になる。 -/
lemma boundedSubcategory_isIdempotentComplete :
    IsIdempotentComplete t.bounded.FullSubcategory := by
  constructor
  intro X p hp
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := X.property
  obtain ⟨Y, hge, hle, i, r, hir, hri⟩ := bounded_idempotent_splits t X.obj a b p.hom
    (congrArg (fun f : X ⟶ X ↦ f.hom) hp)
  let Y' : t.bounded.FullSubcategory := ⟨Y, ⟨⟨a, hge⟩, ⟨b, hle⟩⟩⟩
  exact ⟨Y', ⟨i⟩, ⟨r⟩, ObjectProperty.hom_ext _ hir, ObjectProperty.hom_ext _ hri⟩

/-- 有界 t 構造をもつ圏からその Karoubi 包絡への標準関手は同値になる。 -/
noncomputable def boundedTStructureKaroubiEquivalence (hb : ∀ X : C, t.bounded X) :
    C ≌ Karoubi C := by
  have := isIdempotentComplete_of_bounded_tStructure t hb
  exact toKaroubiEquivalence C

set_option backward.defeqAttrib.useBackward true in
/-- 有界な対象の形式的直和因子は、同じ次数範囲にある実際の対象で表せる。 -/
lemma karoubi_bounded_has_representative (P : Karoubi C) (a b : ℤ)
    [t.IsGE P.X a] [t.IsLE P.X b] :
    ∃ (Y : C), t.IsGE Y a ∧ t.IsLE Y b ∧ Nonempty ((toKaroubi C).obj Y ≅ P) := by
  obtain ⟨Y, hge, hle, i, r, hir, hri⟩ := bounded_idempotent_splits t P.X a b P.p P.idem
  refine ⟨Y, hge, hle, ⟨{
    hom := ⟨i, by simp [← hri, ← assoc, hir]⟩
    inv := ⟨r, by simp [← hri, assoc, hir]⟩
    hom_inv_id := by ext; exact hir
    inv_hom_id := by ext; exact hri }⟩⟩

end SerrePositivity

end BoundedTStructureIdempotentPart

section BoundedTStructureGenerationPart

namespace SerrePositivity

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C] (t : TStructure C) (P : ObjectProperty C)
  [P.IsTriangulated] [P.IsClosedUnderIsomorphisms]
  (hh : t.heart ≤ P)

include hh in
omit [IsTriangulated C] in
/-- heart を含みシフトで閉じた部分圏は、単一次数に集中した対象を含む。 -/
lemma pure_mem_of_heart (X : C) (n : ℤ) [t.IsGE X n] [t.IsLE X n] : P X := by
  have := t.isGE_shift X n n 0 (add_zero n)
  have := t.isLE_shift X n n 0 (add_zero n)
  have h : P (X⟦n⟧) := hh _ ⟨t.le_of_isLE _ 0, t.ge_of_isGE _ 0⟩
  exact (P.prop_shift_iff_of_isStableUnderShift X n).1 h

include hh in
set_option backward.defeqAttrib.useBackward true in
/-- 有限な次数幅の対象は、heart と有限回の切り詰め三角形から生成される。 -/
lemma finiteAmplitude_mem_of_heart (w : ℕ) (X : C) (a : ℤ)
    [t.IsGE X a] [t.IsLE X (a + w)] : P X := by
  induction w generalizing X a with
  | zero =>
    have : t.IsLE X a := by simpa using (inferInstance : t.IsLE X (a + (0 : ℕ)))
    exact pure_mem_of_heart t P hh X a
  | succ w ih =>
    let n : ℤ := a + w
    let T := (t.triangleLEGE n (n + 1) rfl).obj X
    have hle : t.IsLE X (n + 1) := by
      convert (inferInstance : t.IsLE X (a + (w + 1 : ℕ))) using 1
      dsimp [n]
      omega
    have : t.IsGE T.obj₁ a := by dsimp [T]; infer_instance
    have : t.IsLE T.obj₁ (a + w) := by dsimp [T, n]; infer_instance
    have : t.IsGE T.obj₃ (n + 1) := by dsimp [T]; infer_instance
    have : t.IsLE T.obj₃ (n + 1) := by dsimp [T]; infer_instance
    exact P.ext_of_isTriangulatedClosed₂ T (t.triangleLEGE_distinguished n (n + 1) rfl X)
      (ih T.obj₁ a) (pure_mem_of_heart t P hh T.obj₃ (n + 1))

include hh in
/-- heart を含む三角部分圏は全ての t 有界対象を含む。 -/
lemma bounded_le_of_heart : t.bounded ≤ P := by
  rintro X ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  have := t.isLE_of_le X b (a + (b - a).toNat) (by omega)
  exact finiteAmplitude_mem_of_heart t P hh (b - a).toNat X a

variable {D : Type*} [Category* D] [Preadditive D] [HasZeroObject D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  (F : D ⥤ C) [F.CommShift ℤ] [F.IsTriangulated] [F.Full]

/-- 充満な三角関手で heart が持ち上がれば、全 t 有界対象が持ち上がる。 -/
lemma bounded_mem_essImage_of_heart (hheart : t.heart ≤ F.essImage) :
    t.bounded ≤ F.essImage := bounded_le_of_heart t F.essImage hheart

/-- 有界 t 構造の heart に対する持ち上げから、本質的全射性を得る。 -/
lemma essSurj_of_bounded_of_heart (hb : ∀ X : C, t.bounded X)
    (hheart : t.heart ≤ F.essImage) : F.EssSurj :=
  ⟨fun X ↦ bounded_mem_essImage_of_heart t F hheart X (hb X)⟩

end SerrePositivity

end BoundedTStructureGenerationPart
