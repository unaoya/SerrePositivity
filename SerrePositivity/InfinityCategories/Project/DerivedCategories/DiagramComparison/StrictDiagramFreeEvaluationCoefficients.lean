module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictDiagramFreeEvaluationAdjunction

/-!
概要：評価点の添字比較が係数と指定増大射を保つこと。
方針：Over圏の忘却と構造射を使い、余単位での係数移送を恒等射と照合する。
規約：通常の係数の照合であり、導来実現の弱同値性は別に証明する。
使われ方：HTT 4.2.4.4、RR02(a)の重み付き実現への接続。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory CategoryTheory.Limits
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (d : StrictDiagramDirection) (k : strictDiagramIndex d)
variable {C : Type v} [Category.{w} C] (V : strictDiagramIndex d ⥤ C)

/-- 評価点の余積の各項に付く、元の図式の始点での係数。 -/
def strictDiagramFreeEvaluationCoefficients :
    StrictDiagramFreeEvaluationIndex.{u} d k ⥤ C :=
  strictDiagramFreeEvaluationToOver d k ⋙ Over.forget k ⋙ V

/-- 指定した余単位は係数を恒等射で移送する。 -/
lemma strictDiagramFreeEvaluationCoefficients_counit
    (t : StrictDiagramFreeEvaluationIndex.{u} d k) :
    (strictDiagramFreeEvaluationCoefficients d k V).map
        (strictDiagramFreeEvaluationCounitComponent d k t) =
      𝟙 ((strictDiagramFreeEvaluationCoefficients d k V).obj t) := by
  change V.map (𝟙 _) = 𝟙 _
  exact V.map_id _

/-- 合成した射による指定増大射。添字の全射について自然。 -/
def strictDiagramFreeEvaluationCoefficientAugmentation :
    strictDiagramFreeEvaluationCoefficients.{u} d k V ⟶
      (Functor.const (StrictDiagramFreeEvaluationIndex.{u} d k)).obj (V.obj k) where
  app t := V.map ((strictDiagramFreeEvaluationToOver d k).obj t).hom
  naturality := by
    intro t s f
    change V.map _ ≫ V.map _ = V.map _ ≫ 𝟙 _
    rw [Category.comp_id, ← V.map_comp]
    exact congrArg V.map (Over.w ((strictDiagramFreeEvaluationToOver d k).map f))

/-- 恒等射付きの添字に戻しても、指定増大射は同じ合成射の像。 -/
lemma strictDiagramFreeEvaluationCoefficientAugmentation_section (t : Over k) :
    (strictDiagramFreeEvaluationCoefficientAugmentation.{u} d k V).app
        ((strictDiagramFreeEvaluationSection d k).obj t) = V.map t.hom := by
  change V.map (t.hom ≫ 𝟙 k) = V.map t.hom
  rw [Category.comp_id]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
