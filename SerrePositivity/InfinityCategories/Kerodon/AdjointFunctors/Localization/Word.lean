module

public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.Fin.Basic

/-!
# Hammock の有限の向き付き語の添字圏

概要：Dwyer–Kan 1980b §4.1 の二色の有限全順序と色を保つ単調写像を構成する。
方針：長さと各位置の向きを持つ語に、明示的な OrderHom を射として与える。
規約：位置は左から右に数える。空語も含め、filtered 性は仮定しない。
使われ方：固定語の zigzag の nerve を並べる hammock の添字。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory CategoryTheory.Limits

/-- 各列の向き。後ろ向きの列には指定弱同値の条件を付ける。 -/
inductive Direction
  | forward
  | backward
  deriving DecidableEq

/-- 空語を含む、有限の向き付き語。 -/
structure Word where
  length : ℕ
  direction : Fin length → Direction

namespace Word

/-- 語の射は色を保つ単調写像。単射や全射に限定しない。 -/
structure Hom (a b : Word) where
  orderHom : Fin a.length →o Fin b.length
  direction_eq : ∀ i, b.direction (orderHom i) = a.direction i

@[ext] lemma hom_ext {a b : Word} (f g : Hom a b)
    (h : ∀ i, f.orderHom i = g.orderHom i) : f = g := by
  have : f.orderHom = g.orderHom := DFunLike.ext _ _ h
  cases f
  cases g
  cases this
  rfl

/-- 恒等写像と合成は元の単調写像の恒等写像と合成。 -/
instance wordCategory : SmallCategory Word where
  Hom := Hom
  id _ := ⟨OrderHom.id, fun _ => rfl⟩
  comp f g := ⟨g.orderHom.comp f.orderHom, fun i =>
    (g.direction_eq (f.orderHom i)).trans (f.direction_eq i)⟩
  id_comp _ := hom_ext _ _ (fun _ => rfl)
  comp_id _ := hom_ext _ _ (fun _ => rfl)
  assoc _ _ _ := hom_ext _ _ (fun _ => rfl)

@[simp] lemma id_apply (a : Word) (i : Fin a.length) :
    (𝟙 a : a ⟶ a).orderHom i = i := rfl

@[simp] lemma comp_apply {a b c : Word} (f : a ⟶ b) (g : b ⟶ c)
    (i : Fin a.length) : (f ≫ g).orderHom i = g.orderHom (f.orderHom i) := rfl

/-- 空語。固定端点が等しい幅零の hammock を含めるために必要。 -/
def empty : Word := ⟨0, Fin.elim0⟩

/-- 空語から任意の語への唯一の色を保つ単調写像。 -/
def fromEmpty (a : Word) : empty ⟶ a :=
  ⟨⟨Fin.elim0, fun i => Fin.elim0 i⟩, fun i => Fin.elim0 i⟩

lemma fromEmpty_unique (a : Word) (f : empty ⟶ a) : f = fromEmpty a :=
  hom_ext _ _ (fun i => Fin.elim0 i)

/-- 空語は添字圏の始対象。 -/
def emptyIsInitial : IsInitial empty :=
  IsInitial.ofUniqueHom fromEmpty (fun a f => fromEmpty_unique a f)

/-- 一文字の語。 -/
def single (d : Direction) : Word := ⟨1, fun _ => d⟩

/-- 元の三本矢 X ← U → V ← Y の左から右への向き。 -/
def threeArrow : Word := ⟨3, fun i => if i = 1 then .forward else .backward⟩

end Word
end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
