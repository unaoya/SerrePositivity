module

public import SerrePositivity.EInfinity.Hammock.ColimitComposition
public import SerrePositivity.EInfinity.Hammock.ForwardZigzag

/-!
# 元の hammock 合成と生成射の各次数の点

概要：元の合成を各次数の点に適用し、元の生成射の一定単体と標準射を回収する。
方針：既存の colimitComposition と元の graphComposition の回収式を使う。
規約：元の余極限・標準射・全単体作用素を保持する。
使われ方：反復切断列から元の hammock への貼り戻し。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.IsMultiplicative]

variable (X Y Z : C) {n m : SimplexCategoryᵒᵖ}

def composePoint (p : (colimitGraph W X Y).obj n) (q : (colimitGraph W Y Z).obj n) :
    (colimitGraph W X Z).obj n := (colimitComposition W X Y Z).app n (p, q)

lemma composePoint_simplex (θ : n ⟶ m) (p : (colimitGraph W X Y).obj n)
    (q : (colimitGraph W Y Z).obj n) :
    composePoint W X Y Z ((colimitGraph W X Y).map θ p) ((colimitGraph W Y Z).map θ q) =
      (colimitGraph W X Z).map θ (composePoint W X Y Z p q) :=
  congrArg (fun k => k (p, q)) ((colimitComposition W X Y Z).naturality θ)

lemma composePoint_inclusions (a b : Word) (σ : (graph W a X Y).obj n)
    (τ : (graph W b Y Z).obj n) :
    composePoint W X Y Z ((graphInclusion W X Y a).app n σ)
      ((graphInclusion W Y Z b).app n τ) =
      (graphInclusion W X Z (Word.append a b)).app n (σ.prod' τ ⋙ ZigzagAppend.functor) :=
  congrArg (fun k => k.app n (σ, τ)) (colimitComposition_fac W X Y Z a b)

variable {X Y Z}

def arrowSimplex (p : X ⟶ Y) (n : SimplexCategoryᵒᵖ) :
    (graph W (Word.single .forward) X Y).obj n :=
  (Functor.const (Fin (n.unop.len + 1))).obj (ForwardZigzag.obj (W := W) p)

def arrowPoint (p : X ⟶ Y) (n : SimplexCategoryᵒᵖ) : (colimitGraph W X Y).obj n :=
  (graphInclusion W X Y (Word.single .forward)).app n (arrowSimplex W p n)

lemma arrowPoint_simplex (θ : n ⟶ m) (p : X ⟶ Y) :
    (colimitGraph W X Y).map θ (arrowPoint W p n) = arrowPoint W p m :=
  (congrArg (fun k => k (arrowSimplex W p n))
    ((graphInclusion W X Y (Word.single .forward)).naturality θ)).symm

end SerrePositivity.EInfinity.Hammock
