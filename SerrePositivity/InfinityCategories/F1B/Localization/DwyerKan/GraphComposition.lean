module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.NerveProduct
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagAppendFunctor

/-!
# 固定語の hammock graph の単体的合成

概要：二つの固定語の graph の積から連結語の graph への元の単体的射を構成。
方針：nerve の元の積同型と、全縦弱同値を連結する関手の nerve を合成。
規約：全単体・全作用素を保持する。全語の遷移に対する自然性は後続。
使われ方：全語の余極限上の hammock の合成の構成。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.Hammock
open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.IsMultiplicative]
  (a b : Word) (X Y Z : C)

/-- 元の全射列と全縦弱同値を連結する、固定語の graph の単体的合成。 -/
def graphComposition : graph W a X Y ⊗ graph W b Y Z ⟶ graph W (Word.append a b) X Z :=
  NerveProduct.pair _ _ ≫ nerveMap ZigzagAppend.functor

/-- 全単体で、元の二つの射列の積と同じ連結関手を使う。 -/
lemma graphComposition_app (n : SimplexCategoryᵒᵖ)
    (σ : (graph W a X Y).obj n) (τ : (graph W b Y Z).obj n) :
    (graphComposition W a b X Y Z).app n (σ, τ) = σ.prod' τ ⋙ ZigzagAppend.functor := rfl

/-- 全頂点で、元の同じ二つの zigzag を連結する。 -/
lemma graphComposition_vertex (n : SimplexCategoryᵒᵖ)
    (σ : (graph W a X Y).obj n) (τ : (graph W b Y Z).obj n)
    (j : Fin (n.unop.len + 1)) :
    ((graphComposition W a b X Y Z).app n (σ, τ)).obj j =
      ZigzagAppend.obj (σ.obj j) (τ.obj j) := rfl

/-- 全縦射で、元の同じ二つの弱同値の縦射を連結する。 -/
lemma graphComposition_map (n : SimplexCategoryᵒᵖ)
    (σ : (graph W a X Y).obj n) (τ : (graph W b Y Z).obj n)
    {i j : Fin (n.unop.len + 1)} (h : i ⟶ j) :
    ((graphComposition W a b X Y Z).app n (σ, τ)).map h =
      ZigzagAppend.map (σ.map h) (τ.map h) := rfl

end SerrePositivity.EInfinity.Hammock
