module

public import SerrePositivity.EInfinity.Hammock.MarkedValueSpine

/-!
# 元の指定値の因子列の単位と合成

概要：同じ生成矢を保持して列を連結し、接合部の二つの指定値だけを合成する。
方針：元の nil/cons 表示による再帰と元の自由 groupoid の圏法則を使う。
規約：長さ零の指定値も合成へそのまま含める。
使われ方：通常の局所化と比較する元の値の因子列の圏。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.ValueSpine
open CategoryTheory

variable {C : Type u} [Category.{u} C] {W : MorphismProperty C} {X Y Z V : Paths C}

def precompose (p : valueHomType W X Y) : ValueSpine W Z Y → ValueSpine W Z X
  | .nil _ q => .nil X (p ≫ q)
  | .cons _ g q t => .cons X g (p ≫ q) t

def compose {X Y Z : Paths C} : ValueSpine W Y X → ValueSpine W Z Y → ValueSpine W Z X
  | .nil _ p, s => precompose p s
  | .cons _ g p t, s => .cons X g p (compose t s)

lemma precompose_id (t : ValueSpine W Y X) : precompose (𝟙 _) t = t := by
  cases t <;> simp only [precompose, Category.id_comp]

lemma precompose_comp {U : Paths C} (p : valueHomType W X Y) (q : valueHomType W Y U)
    (t : ValueSpine W Z U) : precompose (p ≫ q) t = precompose p (precompose q t) := by
  cases t <;> simp only [precompose, Category.assoc]

lemma compose_precompose {U : Paths C} (p : valueHomType W X U)
    (t : ValueSpine W Y U) (s : ValueSpine W Z Y) :
    compose (precompose p t) s = precompose p (compose t s) := by
  cases t with
  | nil U q => exact precompose_comp p q s
  | cons => rfl

lemma compose_id (t : ValueSpine W Y X) : compose t (nil Y (𝟙 _)) = t := by
  induction t with
  | nil X p => simp only [compose, precompose, Category.comp_id]
  | cons X g p t ih => exact congrArg (cons X g p) ih

lemma id_compose (t : ValueSpine W Y X) : compose (nil X (𝟙 _)) t = t := precompose_id t

lemma compose_assoc (t : ValueSpine W Y X) (s : ValueSpine W Z Y) (r : ValueSpine W V Z) :
    compose (compose t s) r = compose t (compose s r) := by
  induction t with
  | nil X p => exact compose_precompose p s r
  | cons X g p t ih => exact congrArg (cons X g p) ih

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.ValueSpine
