module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Replacements.MiddleBackwardPushout
public import Mathlib.CategoryTheory.MorphismProperty.Factorization

/-!
# 元の中央弱同値の関手的分解の代入

概要：指定されたモデル圏の同じ関手的分解を、元の全体の zigzag に代入する。
方針：弱同値の cofibration 部分は自明と判定し、fibration 部分を左へ伝える。
規約：分解は明示入力。モデル圏だけから関手的分解を仮定しない。
使われ方：中央が自明 cofibration の部分圏への置換と元の counit 成分。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardFactorization
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  {n m : ℕ} {X Y : C}

abbrev intermediate {B D : C} (u : D ⟶ B) : C := cof.Z.obj (Arrow.mk u)
abbrev first {B D : C} (u : D ⟶ B) : D ⟶ intermediate cof u := cof.i.app (Arrow.mk u)
abbrev last {B D : C} (u : D ⟶ B) : intermediate cof u ⟶ B := cof.p.app (Arrow.mk u)

lemma fac {B D : C} (u : D ⟶ B) : first cof u ≫ last cof u = u :=
  congr_app cof.fac (Arrow.mk u)

lemma first_trivialCofibration {B D : C} (u : D ⟶ B) (hu : weakEquivalences C u) :
    trivialCofibrations C (first cof u) := by
  refine ⟨cof.hi _, ?_⟩
  apply (weakEquivalences C).of_postcomp _ (last cof u) (cof.hp _).2
  exact (fac cof u).symm ▸ hu

def input (L : ComposableArrows C n) {D : C} (u : D ⟶ L.obj (Fin.last n)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TerminalReplacement C n := ⟨intermediate cof u, L, last cof u⟩

def obj (L : ComposableArrows C n) (R : ComposableArrows C m)
    (a : L.obj 0 ⟶ X) (ha : weakEquivalences C a)
    (u : R.obj 0 ⟶ L.obj (Fin.last n)) (hu : weakEquivalences C u)
    (b : Y ⟶ R.obj (Fin.last m)) (hb : weakEquivalences C b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (weakEquivalences C) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m) X Y :=
  _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.pullbackObj (input cof L u) (cof.hp _) R a ha u hu (first cof u) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardFactorization.fac cof u) b hb

def projection (L : ComposableArrows C n) (R : ComposableArrows C m)
    (a : L.obj 0 ⟶ X) (ha : weakEquivalences C a)
    (u : R.obj 0 ⟶ L.obj (Fin.last n)) (hu : weakEquivalences C u)
    (b : Y ⟶ R.obj (Fin.last m)) (hb : weakEquivalences C b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Hom (obj cof L R a ha u hu b hb) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.obj L R a ha u hu b hb) :=
  _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.pullbackProjection (input cof L u) (cof.hp _) R a ha u hu (first cof u) (fac cof u) b hb

end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardFactorization
