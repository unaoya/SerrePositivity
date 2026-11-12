module

public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
public import Mathlib.CategoryTheory.Products.Basic
public import Mathlib.CategoryTheory.EqToHom
import all Mathlib.CategoryTheory.Products.Basic
import all Mathlib.CategoryTheory.Functor.Basic

/-!
# strict 図式の全パラメーターに関する評価

## 概要
通常の図式圏の nerve と、持ち上げた添字の nerve の直積から全評価写像を作る。

## 方針
二つの射列の積を通常の評価関手へ送る。各頂点だけの選択をしない。

## 規約
添字圏は小さい宇宙0、値の圏の対象宇宙は u+1。射列の全高次単体を保つ。

## 使われ方
HTT 4.2.4.1、Kerodon 7.5（Tag 039Y）。strict 実現・Tot の指定錐の族の図式側。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet MonoidalCategory
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
variable (J : Type) [SmallCategory J] (C : Type (u + 1)) [Category.{u} C]

/-- 持ち上げた添字の nerve から、元の strict 図式を読む。 -/
def strictDiagramNerve (F : J ⥤ C) :
    (SSet.uliftFunctor.{u + 1, 0}).obj (nerve J) ⟶ nerve C where
  app _ := ↾fun s => s.down ⋙ F
  naturality _ _ _ := rfl

/-- strict 図式の射列と添字の射列を同時に評価する全単体的写像。 -/
def strictDiagramEvaluation :
    nerve (J ⥤ C) ⊗ (SSet.uliftFunctor.{u + 1, 0}).obj (nerve J) ⟶ nerve C where
  app _ := ↾fun s => (s.1.prod' s.2.down) ⋙
    (CategoryTheory.Prod.swap (J ⥤ C) J ⋙ evaluationUncurried J C)
  naturality _ _ _ := rfl

/-- 評価の零単体は、指定した図式の指定した対象での値。 -/
theorem strictDiagramEvaluation_obj (F : J ⥤ C) (j : J) :
    (strictDiagramEvaluation J C).app (Opposite.op ⦋0⦌)
      (ComposableArrows.mk₀ F, ULift.up (ComposableArrows.mk₀ j)) =
        ComposableArrows.mk₀ (F.obj j) := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro i j f
  simp [strictDiagramEvaluation, ComposableArrows.mk₀]

/-- 同じ strict 図式の射列の像は各頂点でその図式の値を持つ。 -/
theorem strictDiagramNerve_obj (F : J ⥤ C) (j : J) :
    (strictDiagramNerve J C F).app (Opposite.op ⦋0⦌)
      (ULift.up (ComposableArrows.mk₀ j)) = ComposableArrows.mk₀ (F.obj j) := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro i j f
  simp [strictDiagramNerve, ComposableArrows.mk₀]

/-- 全評価の各単体の対象は、二つの射列を同じ位置で評価したもの。 -/
theorem strictDiagramEvaluation_value_obj {n : ℕ}
    (F : ComposableArrows (J ⥤ C) n) (s : ComposableArrows J n) (i : Fin (n + 1)) :
    ((strictDiagramEvaluation J C).app (Opposite.op ⦋n⦌) (F, ULift.up s)).obj i =
      (F.obj i).obj (s.obj i) := rfl

/-- 全評価の各単体の射は、図式の射と添字の射を同時に写す標準の合成。 -/
theorem strictDiagramEvaluation_value_map {n : ℕ}
    (F : ComposableArrows (J ⥤ C) n) (s : ComposableArrows J n)
    {i j : Fin (n + 1)} (f : i ⟶ j) :
    ((strictDiagramEvaluation J C).app (Opposite.op ⦋n⦌) (F, ULift.up s)).map f =
      (F.obj i).map (s.map f) ≫ (F.map f).app (s.obj j) := rfl

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
