module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.ComplexDerivedSemifreeComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictSemifreeColimitFamily
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictDiagramEvaluationFactorization
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorComposition

public import Mathlib.CategoryTheory.Whiskering

import all SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictSemifreeColimitFamily

/-!
概要：半自由strict図式の全族を、元の通常複体図式の局所化評価へ接続する。
方針：通常評価の自然性と全nerveの比較を内部Homに運ぶ。
規約：添字はΔ・Δᵒᵖ、パラメーターには全射列を残す。
使われ方：3b-3 R5・R7、strict実現の全族比較の入力。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet MonoidalCategory MonoidalClosed CartesianMonoidalCategory
open scoped Simplicial
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison

variable (A : Type u) [CommRing A] (d : StrictDiagramDirection)

/-- 半自由図式の元の閉零射を通常複体の同じ射として忘れる関手。 -/
def strictSemifreeUnderlyingComplex :
    StrictSemifreeDiagram A (strictDiagramIndex d) ⥤ StrictComplexDiagram A d :=
  (Functor.whiskeringRight _ _ _).obj (semifreeUnderlyingComplex A)

/-- 半自由図式の全評価を、閉零圏の通常nerveの中で読む族。 -/
def strictSemifreeClosedFamily :
    nerve (StrictSemifreeDiagram A (strictDiagramIndex d)) ⟶
      (ihom ((SSet.uliftFunctor.{u + 1, 0}).obj (nerve (strictDiagramIndex d)))).obj
        (nerve (ClosedCategory A (Semifree A))) :=
  curry ((β_ _ _).hom ≫ strictDiagramEvaluation (strictDiagramIndex d)
    (ClosedCategory A (Semifree A)))

/-- 全図式の通常の評価は、値の関手による後合成と可換。 -/
@[reassoc]
lemma strictSemifreeUnderlyingComplex_evaluation :
    (nerveMap (strictSemifreeUnderlyingComplex A d) ▷
      (SSet.uliftFunctor.{u + 1, 0}).obj (nerve (strictDiagramIndex d))) ≫
      strictDiagramEvaluation (strictDiagramIndex d) (Complex A) =
    strictDiagramEvaluation (strictDiagramIndex d) (ClosedCategory A (Semifree A)) ≫
      nerveMap (semifreeUnderlyingComplex A) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨s, t⟩
  refine CategoryTheory.Functor.ext ?_ ?_
  · intro i
    rfl
  intro i j f
  change ((semifreeUnderlyingComplex A).map ((s.obj i).map (t.down.map f))) ≫
      (semifreeUnderlyingComplex A).map ((s.map f).app (t.down.obj j)) =
    (semifreeUnderlyingComplex A).map
      ((s.obj i).map (t.down.map f) ≫ (s.map f).app (t.down.obj j))
  exact ((semifreeUnderlyingComplex A).map_comp _ _).symm

/-- 通常複体図式の評価へ忘れても、元の全族の評価式を保つ。 -/
lemma strictSemifreeUnderlyingComplex_family :
    nerveMap (strictSemifreeUnderlyingComplex A d) ≫ strictComplexDiagramFamily A d =
      strictSemifreeClosedFamily A d ≫
        (ihom ((SSet.uliftFunctor.{u + 1, 0}).obj (nerve (strictDiagramIndex d)))).map
          (nerveMap (semifreeUnderlyingComplex A) ≫ complexDerivedEvaluation A) := by
  rw [strictComplexDiagramFamily, ← curry_natural_left,
    strictSemifreeClosedFamily, ← curry_natural_right]
  apply congrArg curry
  simp only [strictComplexDerivedEvaluation, Category.assoc]
  rw [BraidedCategory.braiding_naturality_right_assoc,
    strictSemifreeUnderlyingComplex_evaluation_assoc]

/-- 半自由の全族の閉nerve表示は、3b-1で指定された元の全族と同じ。 -/
lemma strictSemifreeClosedFamily_inclusion :
    strictSemifreeClosedFamily A d ≫
      (ihom ((SSet.uliftFunctor.{u + 1, 0}).obj (nerve (strictDiagramIndex d)))).map
        (closedNerveInclusion A (Semifree A)) =
      strictSemifreeDiagramFamily A (strictDiagramIndex d) := by
  rw [strictSemifreeClosedFamily, ← curry_natural_right]
  simp only [strictSemifreeDiagramFamily, strictSemifreeEvaluation, Category.assoc]

/-- 全単体を保つ半自由図式の表示比較。対象ごとの選択に依存しない。 -/
def strictSemifreeComplexFamilyIso :
    FunctorIso
      (nerveMap (strictSemifreeUnderlyingComplex A d) ≫ strictComplexDiagramFamily A d)
      (strictSemifreeDiagramFamily A (strictDiagramIndex d)) := by
  rw [strictSemifreeUnderlyingComplex_family,
    ← strictSemifreeClosedFamily_inclusion]
  exact ((complexDerivedEvaluation_semifreeIso A).map_post _).precomp
    (strictSemifreeClosedFamily A d)

/-- 元の局所化を通す評価と、3b-1の半自由図式の全族との比較。 -/
def strictSemifreeLocalizedFamilyIso :
    FunctorIso
      (nerveMap (strictSemifreeUnderlyingComplex A d) ≫
        strictDiagramLocalization A d ≫ strictDiagramDerivedEvaluation A d)
      (strictSemifreeDiagramFamily A (strictDiagramIndex d)) :=
  (strictDiagramDerivedEvaluation_factor A d).precomp
    (nerveMap (strictSemifreeUnderlyingComplex A d)) ≪≫ strictSemifreeComplexFamilyIso A d

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
