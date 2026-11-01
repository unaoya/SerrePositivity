module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.GeneratorBlockEquivalence

/-!
# 交互標準形のブロックと元の二つの生成部分

概要：交互標準形の各単色ブロックを、指定・非指定の生成矢の自由射列へ移す。
方針：色の定義から所属類を照合し、元の指定生成射列の全単射を使う。
規約：元のブロックの射列を包含で厳密に回収する。
使われ方：交互標準形を元の二つの自由因子の射として解釈する。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.SimplicialLocalization.GeneratorBlocks
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)

def part (c : Bool) : MorphismProperty C := if c then W else GeneratorPartition.unmarked W

lemma monochrome_eq_part (c : Bool) : monochrome W c = part W c := by
  ext X Y f
  cases c with
  | false => exact color_false_iff W f
  | true => exact color_true_iff W f

lemma monochrome_paths_iff {X Y : C} (c : Bool) (p : Quiver.Path X Y) :
    (monochrome W c).paths p ↔ (part W c).paths p := by
  rw [monochrome_eq_part]

def typedBlock {X Y : C} (c : Bool) (p : Quiver.Path X Y)
    (hp : (monochrome W c).paths p) :
    Quiver.Path (V := MarkedGenerators.quiver (part W c)) X Y :=
  MarkedGenerators.lift (part W c) p ((monochrome_paths_iff W c p).1 hp)

lemma inclusion_typedBlock {X Y : C} (c : Bool) (p : Quiver.Path X Y)
    (hp : (monochrome W c).paths p) :
    (MarkedGenerators.inclusion (part W c)).map (typedBlock W c p hp) = p :=
  MarkedGenerators.inclusion_lift (part W c) p _

lemma typedBlock_length {X Y : C} (c : Bool) (p : Quiver.Path X Y)
    (hp : (monochrome W c).paths p) : (typedBlock W c p hp).length = p.length := by
  induction p with
  | nil => rfl
  | cons p f ih => exact congrArg Nat.succ (ih hp.1)

lemma normalize_monochrome {X Y : C} (c : Bool) (p : Quiver.Path X Y)
    (positive : 0 < p.length) (uniform : (monochrome W c).paths p) :
    normalize W p =
      ⟨some c, .snoc .nil c p positive uniform (by simp)⟩ := by
  have h := normalize_appendBlock W (show Form W X none X from .nil)
    c p uniform (by simp) rfl
  change normalize W (Quiver.Path.nil.comp p) = _ at h
  rw [Quiver.Path.nil_comp] at h
  exact h.trans (appendBlock_positive W .nil c p positive uniform (by simp))

lemma normalize_toPath {X Y : C} (f : X ⟶ Y) :
    normalize W f.toPath =
      ⟨some (color W f), .snoc .nil (color W f) f.toPath
        (by simp) ⟨trivial, rfl⟩ (by simp)⟩ := rfl

lemma normalize_letter_ne_empty {X : C} (f : X ⟶ X) :
    normalize W f.toPath ≠ empty W X := by
  intro h
  have he := congrArg Sigma.fst h
  cases he

end SerrePositivity.EInfinity.SimplicialLocalization.GeneratorBlocks
