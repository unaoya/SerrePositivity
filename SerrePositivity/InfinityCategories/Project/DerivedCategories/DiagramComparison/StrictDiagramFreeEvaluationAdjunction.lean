module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictDiagramFreeEvaluationCounit
public import Mathlib.CategoryTheory.Adjunction.Basic

/-!
概要：評価点の実余積の添字圏とOver圏との随伴。
方針：恒等射による単位と既存の余単位を使い、両三角恒等式を全成分で照合する。
規約：指定済みの二つの関手をそのまま使う。重みの実現後の弱同値性は別に示す。
使われ方：HTT 4.2.4.4のRR02(a)、評価点での増大射の比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (d : StrictDiagramDirection) (k : strictDiagramIndex d)

/-- 恒等射を付けて合成すると元のOver対象に戻る、指定した単位。 -/
def strictDiagramFreeEvaluationUnit :
    𝟭 (Over k) ⟶ strictDiagramFreeEvaluationSection.{u} d k ⋙
      strictDiagramFreeEvaluationToOver d k where
  app t := Over.homMk (𝟙 t.left) (by
    change 𝟙 t.left ≫ (t.hom ≫ 𝟙 k) = t.hom
    simp)
  naturality := by
    intro t s f
    apply (Over.forget k).map_injective
    change f.left ≫ 𝟙 s.left = 𝟙 t.left ≫ f.left
    simp

/-- 同じ単位と余単位の左三角恒等式。 -/
lemma strictDiagramFreeEvaluation_left_triangle :
    Functor.whiskerRight (strictDiagramFreeEvaluationUnit.{u} d k)
        (strictDiagramFreeEvaluationSection d k) ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (strictDiagramFreeEvaluationSection d k)
        (strictDiagramFreeEvaluationCounit d k) =
      𝟙 (𝟭 (Over k) ⋙ strictDiagramFreeEvaluationSection d k) := by
  apply NatTrans.ext
  funext t
  apply Functor.Elements.Hom.ext
  apply Quiver.Hom.unop_inj
  apply Functor.Elements.Hom.ext
  apply Prod.ext <;>
    simp [strictDiagramFreeEvaluationUnit, strictDiagramFreeEvaluationSection,
      strictDiagramFreeEvaluationCounit, strictDiagramFreeEvaluationCounitComponent,
      strictDiagramFreeEvaluationSectionObj]
  all_goals rfl

/-- 同じ単位と余単位の右三角恒等式。 -/
lemma strictDiagramFreeEvaluation_right_triangle :
    Functor.whiskerLeft (strictDiagramFreeEvaluationToOver.{u} d k)
        (strictDiagramFreeEvaluationUnit d k) ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (strictDiagramFreeEvaluationCounit d k)
        (strictDiagramFreeEvaluationToOver d k) =
      𝟙 (strictDiagramFreeEvaluationToOver d k ⋙ 𝟭 (Over k)) := by
  apply NatTrans.ext
  funext t
  apply (Over.forget k).map_injective
  change 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ = 𝟙 _
  simp

/-- 恒等射を付ける関手は、合成への指定関手の左随伴。 -/
def strictDiagramFreeEvaluationAdjunction :
    strictDiagramFreeEvaluationSection.{u} d k ⊣ strictDiagramFreeEvaluationToOver d k :=
  Adjunction.mkOfUnitCounit
    { unit := strictDiagramFreeEvaluationUnit d k
      counit := strictDiagramFreeEvaluationCounit d k
      left_triangle := strictDiagramFreeEvaluation_left_triangle d k
      right_triangle := strictDiagramFreeEvaluation_right_triangle d k }

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
