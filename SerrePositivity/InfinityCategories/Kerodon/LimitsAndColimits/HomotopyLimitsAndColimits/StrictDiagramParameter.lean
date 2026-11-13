module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.StrictDiagramEvaluation
import all SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.StrictDiagramEvaluation
import all Mathlib.CategoryTheory.Functor.Basic
import all Mathlib.CategoryTheory.Products.Basic

/-!
# 全評価を指定した strict 図式へ制限する

## 概要
図式のパラメーターを固定する全単体的射を作り、全評価の制限が同じ元の図式になることを示す。

## 方針
パラメーター側に定数射列を置き、添字の射列をそのまま保つ。

## 規約
頂点の一致だけでなく、添字の全高次単体で写像の等式を与える。

## 使われ方
HTT 4.2.4.1、Kerodon 7.5（Tag 039Y）。指定 join 錐の族の strict 図式への制限。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet MonoidalCategory
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
variable (J : Type) [SmallCategory J] (C : Type (u + 1)) [Category.{u} C]

/-- 図式のパラメーターを固定し、添字の全射列を保つ写像。 -/
def strictDiagramParameter (F : J ⥤ C) :
    (SSet.uliftFunctor.{u + 1, 0}).obj (nerve J) ⟶
      nerve (J ⥤ C) ⊗ (SSet.uliftFunctor.{u + 1, 0}).obj (nerve J) where
  app d := ↾fun s => ((Functor.const (Fin (d.unop.len + 1))).obj F, s)
  naturality _ _ _ := rfl

/-- 全評価をパラメーターで制限すると、指定された同じ strict 図式の全 nerve 写像になる。 -/
theorem strictDiagramParameter_evaluation (F : J ⥤ C) :
    strictDiagramParameter J C F ≫ strictDiagramEvaluation J C = strictDiagramNerve J C F := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro s
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro i j f
  simp [strictDiagramParameter, strictDiagramEvaluation, strictDiagramNerve]

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
