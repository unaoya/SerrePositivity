module

public import SerrePositivity.EInfinity.Hammock.MarkedSpineComposition

/-!
# 元の全因子列の単体的合成と抽出・貼り戻しの合成保存

概要：明示的な合成を単体写像にし、元の二つの同型射の合成保存を回収する。
方針：全単体作用素への整合と貼り戻しの単射性を使う。
規約：同型による抽象的な移送で明示的な合成を定義しない。
使われ方：元の自由積の豊穣合成と普遍性。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine
open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{u} C] {W : MorphismProperty C}
  {X Y Z : Paths C} {n : SimplexCategoryᵒᵖ}

lemma glue_injective : Function.Injective (glue : MarkedSpine W Y n X → _) := by
  intro s t h
  exact (markedSpine_glue W Y s).symm.trans
    ((congrArg (markedSpine W Y n X) h).trans (markedSpine_glue W Y t))

lemma append_word (s : MarkedSpine W Y n X) (t : MarkedSpine W Z n Y) :
    (append s t).word = List.append s.word t.word := by
  induction s with
  | nil X p => cases t <;> rfl
  | cons X g p s ih => exact congrArg (List.cons g.val) ih

lemma extraction_composePoint (p : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W.paths X Y).obj n)
    (q : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W.paths Y Z).obj n) :
    markedSpine W Z n X (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composePoint W.paths X Y Z p q) =
      append (markedSpine W Y n X p) (markedSpine W Z n Y q) := by
  apply glue_injective
  rw [glue_markedSpine, glue_append, glue_markedSpine, glue_markedSpine]

def composition (W : MorphismProperty C) (X Y Z : Paths C) :
    space W Y X ⊗ space W Z Y ⟶ space W Z X where
  app _ := ↾fun p => append p.1 p.2
  naturality _ _ θ := by
    apply ConcreteCategory.hom_ext
    intro p
    exact append_simplex θ p.1 p.2

lemma composition_gluing (W : MorphismProperty C) (X Y Z : Paths C) :
    composition W X Y Z ≫ gluing W Z X =
      (gluing W Y X ⊗ₘ gluing W Z Y) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitComposition W.paths X Y Z := by
  ext n p
  exact glue_append p.1 p.2

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine
