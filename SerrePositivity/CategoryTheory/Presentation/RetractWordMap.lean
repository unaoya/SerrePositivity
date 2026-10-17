module

public import SerrePositivity.CategoryTheory.Presentation.RetractWordRealization

/-!
# 中断した任意モデル源への一般化：RetractWordMap

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Functoriality of the retract-word presentation in source and word parameters。

## 方針（定義・証明）
自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0027][inventory]を参照する。

[inventory]: ../../../formalization-plans/k-theory-generalization-inventory.md#m0027
[plan]: ../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Functoriality of the retract-word presentation in source and word parameters
-/

@[expose] public section
universe u v w u' v' w' u'' v'' w''
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.RetractWords
variable {C : Type u} [Category.{v} C] {M : Type w} [MonoidWithZero M]
  {C' : Type u'} [Category.{v'} C'] {N : Type w'} [MonoidWithZero N]

def mapRealization (F : C ⥤ C') (h : M →*₀ N) : Realization C M (Obj C' N) where
  ambient := F ⋙ sourceFunctor C' N
  small X := (quotient C' N).obj (.small (F.obj X))
  section_ X := (quotient C' N).map (section_ C' N (F.obj X))
  projection X := (quotient C' N).map (projection C' N (F.obj X))
  action X t := (quotient C' N).map (word C' N (F.obj X) (h t))
  action_one X := by
    dsimp [sourceFunctor]
    simpa only [map_one, Functor.map_id] using
      CategoryTheory.Quotient.sound (Rel C' N) (Rel.word_one (F.obj X))
  action_mul X t z := by
    simpa using (CategoryTheory.Quotient.sound (Rel C' N)
      (Rel.word_mul (F.obj X) (h t) (h z))).symm
  split X := by
    simpa using CategoryTheory.Quotient.sound (Rel C' N) (Rel.split (F.obj X))
  action_zero X := by
    simpa using CategoryTheory.Quotient.sound (Rel C' N) (Rel.word_zero (F.obj X))
  section_action X t := by
    simpa using CategoryTheory.Quotient.sound (Rel C' N) (Rel.section_word (F.obj X) (h t))
  action_projection X t := by
    simpa using CategoryTheory.Quotient.sound (Rel C' N) (Rel.word_projection (F.obj X) (h t))

def map (F : C ⥤ C') (h : M →*₀ N) : Obj C M ⥤ Obj C' N := (mapRealization F h).functor

lemma map_source (F : C ⥤ C') (h : M →*₀ N) {X Y : C} (f : X ⟶ Y) :
    (map F h).map ((quotient C M).map (source C M f)) =
      (quotient C' N).map (source C' N (F.map f)) :=
  (mapRealization F h).functor_source f

lemma map_word (F : C ⥤ C') (h : M →*₀ N) (X : C) (t : M) :
    (map F h).map ((quotient C M).map (word C M X t)) =
      (quotient C' N).map (word C' N (F.obj X) (h t)) :=
  (mapRealization F h).functor_word X t

lemma map_section (F : C ⥤ C') (h : M →*₀ N) (X : C) :
    (map F h).map ((quotient C M).map (section_ C M X)) =
      (quotient C' N).map (section_ C' N (F.obj X)) :=
  (mapRealization F h).functor_section X

lemma map_projection (F : C ⥤ C') (h : M →*₀ N) (X : C) :
    (map F h).map ((quotient C M).map (projection C M X)) =
      (quotient C' N).map (projection C' N (F.obj X)) :=
  (mapRealization F h).functor_projection X

lemma map_id_raw {X Y : Raw C M} (p : X ⟶ Y) :
    HEq ((map (𝟭 C) (MonoidWithZeroHom.id M)).map ((quotient C M).map p))
      ((quotient C M).map p) := by
  induction p with
  | nil => cases X <;> rfl
  | cons p e ih =>
    cases e <;> cases X <;>
      simp_all [map, mapRealization, Realization.functor, Realization.raw, Realization.edges,
        sourceFunctor, Paths.lift, CategoryTheory.Quotient.lift, Quot.liftOn,
        CategoryTheory.Quotient.functor] <;> rfl

lemma map_id : map (𝟭 C) (MonoidWithZeroHom.id M) = 𝟭 (Obj C M) := by
  apply CategoryTheory.Quotient.lift_unique' (Rel C M)
  refine CategoryTheory.Functor.hext
    (F := quotient C M ⋙ map (𝟭 C) (MonoidWithZeroHom.id M))
    (G := quotient C M ⋙ 𝟭 (Obj C M)) (fun X => by cases X <;> rfl) ?_
  intro X Y p
  exact map_id_raw p

variable {C'' : Type u''} [Category.{v''} C''] {O : Type w''} [MonoidWithZero O]

lemma map_comp_raw (F : C ⥤ C') (G : C' ⥤ C'') (h : M →*₀ N) (k : N →*₀ O)
    {X Y : Raw C M} (p : X ⟶ Y) :
    HEq ((map (F ⋙ G) (k.comp h)).map ((quotient C M).map p))
      ((map G k).map ((map F h).map ((quotient C M).map p))) := by
  induction p with
  | nil => cases X <;> rfl
  | cons p e ih =>
    cases e <;> cases X <;>
      simp_all [map, mapRealization, Realization.functor, Realization.raw, Realization.edges,
        sourceFunctor, Paths.lift, CategoryTheory.Quotient.lift, Quot.liftOn,
        CategoryTheory.Quotient.functor] <;> rfl

lemma map_comp (F : C ⥤ C') (G : C' ⥤ C'') (h : M →*₀ N) (k : N →*₀ O) :
    map (F ⋙ G) (k.comp h) = map F h ⋙ map G k := by
  apply CategoryTheory.Quotient.lift_unique' (Rel C M)
  refine CategoryTheory.Functor.hext
    (F := quotient C M ⋙ map (F ⋙ G) (k.comp h))
    (G := quotient C M ⋙ (map F h ⋙ map G k)) (fun X => by cases X <;> rfl) ?_
  intro X Y p
  exact map_comp_raw F G h k p

end SerrePositivity.RetractWords
