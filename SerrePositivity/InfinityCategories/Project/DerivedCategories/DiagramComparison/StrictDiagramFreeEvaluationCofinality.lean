module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictDiagramFreeEvaluationAdjunction
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.NerveFinalInitialComma
public import Mathlib.CategoryTheory.Adjunction.Comma

/-!
概要：評価点の指定添字比較の nerve は right cofinal。
方針：Over圏を同じ宇宙へ移し、指定随伴の単位が与える comma の始対象を使う。
規約：通常の Final 性で済ませず、指定した nerve 写像の高次 cofinal 性を示す。
使われ方：HTT 4.2.4.4のRR02(a)、評価点での重みの移送。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (d : StrictDiagramDirection) (k : strictDiagramIndex d)

/-- 同じ宇宙のOver圏へ向かう、指定した合成関手。 -/
def strictDiagramFreeEvaluationSmallToOver :
    StrictDiagramFreeEvaluationIndex.{u} d k ⥤ AsSmall.{u} (Over k) :=
  strictDiagramFreeEvaluationToOver d k ⋙ AsSmall.up

/-- 元の随伴をOver圏の宇宙変更に沿って運ぶ。 -/
def strictDiagramFreeEvaluationSmallAdjunction :
    AsSmall.down ⋙ strictDiagramFreeEvaluationSection.{u} d k ⊣
      strictDiagramFreeEvaluationSmallToOver d k :=
  AsSmall.equiv.symm.toAdjunction.comp (strictDiagramFreeEvaluationAdjunction d k)

/-- 指定随伴の各単位による始対象から得られる、同じ nerve 射の right cofinal 性。 -/
lemma strictDiagramFreeEvaluation_nerve_isRightCofinal :
    SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal
      (nerveMap (strictDiagramFreeEvaluationSmallToOver.{u} d k)) := by
  apply SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.nerveMap_isRightCofinal_of_initial_comma
  intro q
  exact ⟨StructuredArrow.mk ((strictDiagramFreeEvaluationSmallAdjunction d k).unit.app q),
    ⟨mkInitialOfLeftAdjoint _ (strictDiagramFreeEvaluationSmallAdjunction d k) q⟩⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
