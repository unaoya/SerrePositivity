module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictModuleFamilyEvaluationComparison
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.SmallDiagramShape
public import Mathlib.CategoryTheory.Whiskering

/-!
概要：元の全HA評価を通常の全strict評価へ戻し、値の関手との自然性を示す。
方針：既存の対角の比較と、通常の評価の全有限射列を用いる。
規約：全射・全単体を保つ。対象の値だけの比較ではない。
使われ方：3b-3 R6 U31の係数移送の前提計算。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet MonoidalCategory SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A] (J : Type) [SmallCategory J]

/-- U31の前提計算：同じ元の全HA評価は通常の全strict評価である。 -/
lemma strictModuleFamily_evaluation_factor {C : Type (u + 1)} [Category.{u} C]
    (T : C ⥤ (J ⥤ ModuleCategory A PUnit.{1})) :
    (nerveMap T ▷ (SSet.uliftFunctor.{u + 1, u}).obj
        ((SSet.uliftFunctor.{u, 0}).obj (nerve J))) ≫
      (strictModuleCoherentFamily A J (𝟭 (J ⥤ ModuleCategory A PUnit.{1}))).evaluation =
    (nerve C ◁ (smallDiagramShapeIso.{u} (nerve J)).hom) ≫
      (nerveMap T ▷ (SSet.uliftFunctor.{u + 1, 0}).obj (nerve J)) ≫
      strictDiagramEvaluation J (ModuleCategory A PUnit.{1}) ≫
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveInclusion A (RightModule A PUnit.{1}) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨d, ⟨⟨s⟩⟩⟩
  exact strictModuleCoherentFamily_diagonal A J (𝟭 _) (d ⋙ T) s

/-- U31の前提計算：全strict評価は値の通常関手による後合成に自然である。 -/
lemma strictDiagramEvaluation_postcompose {C D : Type (u + 1)}
    [Category.{u} C] [Category.{u} D] (V : C ⥤ D) :
    (nerveMap ((Functor.whiskeringRight J C D).obj V) ▷
        (SSet.uliftFunctor.{u + 1, 0}).obj (nerve J)) ≫ strictDiagramEvaluation J D =
      strictDiagramEvaluation J C ≫ nerveMap V := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨d, ⟨s⟩⟩
  apply CategoryTheory.Functor.hext
  · intro i
    rfl
  · intro i j f
    apply heq_of_eq
    change V.map ((d.obj i).map (s.map f)) ≫ V.map ((d.map f).app (s.obj j)) =
      V.map ((d.obj i).map (s.map f) ≫ (d.map f).app (s.obj j))
    exact (V.map_comp _ _).symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
