module

public import Mathlib.Combinatorics.Quiver.Path

/-!
# 対象を固定する辺の写像の交わりが道への写像でも保たれる

## 概要
対象を固定する辺の写像の交わりが道への写像でも保たれる。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
生成辺と空の道を指定し、道の長さに関する帰納で射を比較する。
連結との交換から関手または自然変換の法則を確認する。

## 規約と注意
圏・対象・射の宇宙と必要な極限の仮定は各宣言に従う。
表示された圏や比較射を、局所化後の同型だけで置き換えない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はS-構成に現れる圏のnerve、射列、図式間の自然なホモトピーに利用できる。
[棚卸し m0034][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0034
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Path maps preserve intersections of identity-on-object edge maps

The hypotheses concern actual edge maps. A common preimage path is built
edge by edge, retaining all intermediate vertices. No freeness or lifting
assumption on a category with relations is made.
-/

@[expose] public section
universe u vA vB vD vK
open Quiver

namespace SerrePositivity.QuiverPaths
variable {V : Type u}

abbrev EdgeMap (A : Quiver.{vA} V) (B : Quiver.{vB} V) :=
  ∀ {X Y : V}, @Quiver.Hom V A X Y → @Quiver.Hom V B X Y

def edgeFunctor {A : Quiver.{vA} V} {B : Quiver.{vB} V} (f : EdgeMap A B) :
    @Prefunctor V A V B :=
  @Prefunctor.mk V A V B (fun X => X) (fun {_ _} e => f e)

def mapPath {A : Quiver.{vA} V} {B : Quiver.{vB} V} (f : EdgeMap A B)
    {X Y : V} (p : @Path V A X Y) : @Path V B X Y :=
  @Prefunctor.mapPath V A V B (edgeFunctor (A := A) (B := B) f) X Y p

@[simp] lemma mapPath_cons {A : Quiver.{vA} V} {B : Quiver.{vB} V} (f : EdgeMap A B)
    {X Y Z : V} (p : @Path V A X Y) (e : @Quiver.Hom V A Y Z) :
    mapPath f (@Path.cons V A X Y Z p e) = @Path.cons V B X Y Z (mapPath f p) (f e) := rfl

@[simp] lemma mapPath_singleton {A : Quiver.{vA} V} {B : Quiver.{vB} V} (f : EdgeMap A B)
    {X Y : V} (e : @Quiver.Hom V A X Y) :
    mapPath f (@Quiver.Hom.toPath V A X Y e) = @Quiver.Hom.toPath V B X Y (f e) := rfl

lemma mapPath_length {A : Quiver.{vA} V} {B : Quiver.{vB} V} (f : EdgeMap A B)
    {X Y : V} (p : @Path V A X Y) :
    @Path.length V B X Y (mapPath f p) = @Path.length V A X Y p := by
  induction p with
  | nil => rfl
  | cons p e ih => exact congrArg Nat.succ ih

lemma singleton_injective {A : Quiver.{vA} V} {X Y : V} :
    Function.Injective (@Quiver.Hom.toPath V A X Y) := by
  intro f g h
  cases h
  rfl

lemma singleton_of_length_one {A : Quiver.{vA} V} {X Y : V} (p : @Path V A X Y)
    (h : p.length = 1) : ∃ e : @Quiver.Hom V A X Y, p = @Quiver.Hom.toPath V A X Y e := by
  cases p with
  | nil => simp at h
  | @cons Z Y p e =>
    have hp : p.length = 0 := by simpa only [Path.length_cons, Nat.add_eq_right] using h
    obtain rfl := Path.eq_of_length_zero p hp
    obtain rfl := Path.eq_nil_of_length_zero p hp
    exact ⟨e, rfl⟩

lemma mapPath_eq_singleton {A : Quiver.{vA} V} {B : Quiver.{vB} V} (f : EdgeMap A B)
    {X Y : V} (p : @Path V A X Y) (e : @Quiver.Hom V B X Y)
    (h : mapPath f p = @Quiver.Hom.toPath V B X Y e) :
    ∃ d : @Quiver.Hom V A X Y, p = @Quiver.Hom.toPath V A X Y d ∧ f d = e := by
  have hp : @Path.length V A X Y p = 1 := by
    have hl := congrArg (@Path.length V B X Y) h
    simpa only [mapPath_length, Path.length_toPath] using hl
  obtain ⟨d, rfl⟩ := singleton_of_length_one p hp
  exact ⟨d, rfl, singleton_injective h⟩

lemma mapPath_injective {A : Quiver.{vA} V} {B : Quiver.{vB} V} (f : EdgeMap A B)
    (hf : ∀ X Y, Function.Injective (f (X := X) (Y := Y))) {X Y : V} :
    Function.Injective (fun p : @Path V A X Y => mapPath f p) := by
  intro p
  induction p with
  | nil =>
    intro q h
    cases q with
    | nil => rfl
    | cons q e => cases h
  | @cons Y Z p e ih =>
    intro q h
    cases q with
    | nil => cases h
    | @cons Y' Z q d =>
      simp only [mapPath_cons, Path.cons.injEq] at h
      obtain rfl := h.1
      have hp := ih h.2.1.eq
      have he := hf _ _ h.2.2.eq
      subst q; subst d
      rfl

lemma mapPath_concat {A : Quiver.{vA} V} {B : Quiver.{vB} V} (f : EdgeMap A B)
    {X Y Z : V} (p : @Path V A X Y) (q : @Path V A Y Z) :
    mapPath f (@Path.comp V A X Y Z p q) =
      @Path.comp V B X Y Z (mapPath f p) (mapPath f q) := by
  induction q with
  | nil => rfl
  | cons q e ih =>
    change @Path.cons V B X _ _ (mapPath f (@Path.comp V A X Y _ p q)) (f e) = _
    rw [ih]
    rfl

lemma mapPath_comp {A : Quiver.{vA} V} {B : Quiver.{vB} V} {D : Quiver.{vD} V}
    (f : EdgeMap A B) (g : EdgeMap B D) {X Y : V} (p : @Path V A X Y) :
    mapPath g (mapPath f p) = mapPath (fun e => g (f e)) p := by
  induction p with
  | nil => rfl
  | cons p e ih => change (mapPath g (mapPath f p)).cons _ = _; rw [ih]; rfl

lemma mapPath_congr {A : Quiver.{vA} V} {B : Quiver.{vB} V} (f g : EdgeMap A B)
    (h : ∀ {X Y} (e : @Quiver.Hom V A X Y), f e = g e) {X Y : V} (p : @Path V A X Y) :
    mapPath f p = mapPath g p := by
  induction p with
  | nil => rfl
  | cons p e ih => rw [mapPath_cons, mapPath_cons, ih, h e]

/-- 対象を固定する辺の写像の交わりが道への写像でも保たれる。

圏・対象・射の宇宙と必要な極限の仮定は各宣言に従う。
生成辺と空の道を指定し、道の長さに関する帰納で射を比較する。
連結との交換から関手または自然変換の法則を確認する。
-/
lemma mapPath_intersection {A : Quiver.{vA} V} {B : Quiver.{vB} V}
    {D : Quiver.{vD} V} {K : Quiver.{vK} V}
    (f : EdgeMap A D) (g : EdgeMap B D) (a : EdgeMap K A) (b : EdgeMap K B)
    (h : ∀ {X Y} (x : @Quiver.Hom V A X Y) (y : @Quiver.Hom V B X Y), f x = g y →
      ∃ z : @Quiver.Hom V K X Y, a z = x ∧ b z = y)
    {X Y : V} (p : @Path V A X Y) (q : @Path V B X Y) (hpq : mapPath f p = mapPath g q) :
    ∃ r : @Path V K X Y, mapPath a r = p ∧ mapPath b r = q := by
  induction p with
  | nil =>
    cases q with
    | nil => exact ⟨.nil, rfl, rfl⟩
    | cons q e => cases hpq
  | @cons Y Z p e ih =>
    cases q with
    | nil => cases hpq
    | @cons Y' Z q d =>
      simp only [mapPath_cons, Path.cons.injEq] at hpq
      obtain rfl := hpq.1
      obtain ⟨r, hr, hr'⟩ := ih q hpq.2.1.eq
      obtain ⟨z, hz, hz'⟩ := h e d hpq.2.2.eq
      exact ⟨r.cons z, by rw [mapPath_cons, hr, hz], by rw [mapPath_cons, hr', hz']⟩

end SerrePositivity.QuiverPaths
