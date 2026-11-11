module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeRelativeCategory
public import Mathlib.Combinatorics.Quiver.Subquiver

/-!
# 指定した生成矢だけからなる元の自由射列

概要：W の生成矢の自由圏を、元の Paths C の W.paths の射と照合する。
方針：生成矢の subtype quiver からの包含と、全文字の所属証明による逆を構成する。
規約：元の恒等射も一文字の生成矢として保持し、空列と区別する。
使われ方：Dwyer–Kan 比較補題2.3の自由な指定矢の圏。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)

def quiver : WideSubquiver C := fun _ _ f => W f

def forget : quiver W ⥤q C where
  obj X := X
  map f := f.val

def inclusion : Paths (quiver W) ⥤ Paths C := Cat.freeMap (forget W)

def lift {X : C} : ∀ {Y : C} (p : Quiver.Path X Y), W.paths p →
    Quiver.Path (V := quiver W) X Y
  | _, .nil, _ => .nil
  | _, .cons p f, hp => (lift p hp.1).cons ⟨f, hp.2⟩

lemma inclusion_lift {X Y : C} (p : Quiver.Path X Y) (hp : W.paths p) :
    (inclusion W).map (lift W p hp) = p := by
  induction p with
  | nil => rfl
  | cons p f ih => exact congrArg (fun q => q.cons f) (ih hp.1)

lemma inclusion_mem {X Y : quiver W} (p : Quiver.Path X Y) :
    W.paths ((inclusion W).map p) := by
  induction p with
  | nil => trivial
  | cons p f ih => exact ⟨ih, f.property⟩

lemma lift_inclusion {X Y : quiver W} (p : Quiver.Path X Y)
    (hp : W.paths ((inclusion W).map p)) :
    lift W ((inclusion W).map p) hp = p := by
  induction p with
  | nil => rfl
  | cons p f ih => exact congrArg (fun q => q.cons f) (ih hp.1)

def homEquiv (X Y : C) :
    Quiver.Path (V := quiver W) X Y ≃ {p : Quiver.Path X Y // W.paths p} where
  toFun p := ⟨(inclusion W).map p, inclusion_mem W p⟩
  invFun p := lift W p.val p.property
  left_inv p := lift_inclusion W p _
  right_inv p := Subtype.ext (inclusion_lift W p.val p.property)

lemma inclusion_injective (X Y : quiver W) :
    Function.Injective (fun p : Quiver.Path X Y => (inclusion W).map p) := by
  intro p q h
  apply (homEquiv W X Y).injective
  exact Subtype.ext h

lemma inclusion_range {X Y : C} (p : Quiver.Path X Y) :
    (∃ q : Quiver.Path (V := quiver W) X Y, (inclusion W).map q = p) ↔ W.paths p := by
  constructor
  · rintro ⟨q, rfl⟩
    exact inclusion_mem W q
  · intro hp
    exact ⟨lift W p hp, inclusion_lift W p hp⟩

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths
