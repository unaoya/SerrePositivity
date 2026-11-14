module


public meta import SerrePositivity.Util.Citation
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Idempotents.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal

/-!
# 自然な射の族と始対象

## 概要
固定した対象から各対象への自然な射の族があれば、その自己射を分裂させて始対象を得る。

## 方針
自然性から冪等性と、分裂した対象からの射の一意性を示す。

## 規約
BS 著者版 Lemma 7.8 の通常の圏の形。

## 使われ方
離散な評価を持つ prismatic site の始対象。
-/

public noncomputable section

universe u v

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] (X : C)

/-- 概要：自然な脚の自己射を分裂させると始対象が得られる。
方針：分裂の射に自然性を適用し、分裂先での脚が分裂の射自身であることを使う。
規約：BS 著者版 Lemma 7.8 の自然な脚での表示。
使われ方：始対象の分裂を指定して追跡する。 -/
theorem initial_of_natural_legs [IsIdempotentComplete C]
    (a : ∀ Y : C, X ⟶ Y) (ha : ∀ {Y Z : C} (f : Y ⟶ Z), a Y ≫ f = a Z) :
    ∃ (Y : C) (r : X ⟶ Y) (s : Y ⟶ X),
      s ≫ r = 𝟙 Y ∧ r ≫ s = a X ∧ Nonempty (IsInitial Y) := by
  obtain ⟨Y, s, r, hsr, hrs⟩ :=
    IsIdempotentComplete.idempotents_split X (a X) (ha (a X))
  have hr : a Y = r := by
    rw [← ha r, ← hrs, Category.assoc, hsr, Category.comp_id]
  refine ⟨Y, r, s, hsr, hrs, ⟨IsInitial.ofUniqueHom (fun Z ↦ s ≫ a Z) ?_⟩⟩
  intro Z f
  rw [← ha f, hr, ← Category.assoc, hsr, Category.id_comp]

/-- 概要：恒等関手が対象 X の下の圏を経由すると、対応する冪等射の分裂は始対象。
方針：下の圏の三角形を恒等関手に移し、自然な脚の定理を適用する。
規約：BS 著者版 Lemma 7.8。
使われ方：評価の関手から始対象を得る。 -/
theorem initial_of_retraction_idempotent [IsIdempotentComplete C]
    (F : C ⥤ Under X) (hF : F ⋙ Under.forget X = 𝟭 C) :
    ∃ (Y : C) (r : X ⟶ Y) (s : Y ⟶ X), s ≫ r = 𝟙 Y ∧
      r ≫ s = (F.obj X).hom ≫ eqToHom (congrArg (fun G : C ⥤ C ↦ G.obj X) hF) ∧
      Nonempty (IsInitial Y) := by
  let e := eqToHom hF
  let a (Y : C) : X ⟶ Y := (F.obj Y).hom ≫ e.app Y
  have hn {Y Z : C} (f : Y ⟶ Z) : a Y ≫ f = a Z := by
    change ((F.obj Y).hom ≫ e.app Y) ≫ (𝟭 C).map f = (F.obj Z).hom ≫ e.app Z
    rw [Category.assoc, ← e.naturality f, ← Category.assoc]
    exact congrArg (fun g ↦ g ≫ e.app Z) (Under.w (F.map f))
  simpa only [a, e, eqToHom_app] using initial_of_natural_legs X a hn

end CategoryTheory

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Lemma 7.8"] _root_.CategoryTheory.initial_of_natural_legs
attribute [cite BS19 "Lemma 7.8"] _root_.CategoryTheory.initial_of_retraction_idempotent
