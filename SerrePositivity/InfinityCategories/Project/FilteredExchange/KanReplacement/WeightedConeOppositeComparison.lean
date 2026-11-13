module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.WeightedCones.ReflectedWeightedSectionsEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedSections
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.WeightedCones.WeightedSectionsOpposite

/-!
概要：重みの反転同型は通常の錐からの標準比較を反転した錐の比較に送る。
方針：end の各射影を uncurry し、反転した評価と元の錐の第二射影を比較する。
規約：図式と錐の Kan 性は不要。
使われ方：反転 augmentation の Hom 比較を native な余極限判定に接続する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange.WeightedConeOppositeComparison
variable {I : Type u} [SmallCategory I]
local instance : SSet.opFunctor.{u}.IsEquivalence := SSet.opEquivalence.isEquivalence_functor

/-- 概要：反転した重み付き切断の同型は錐の標準比較と可換。
方針：各成分で uncurry した評価を元の比較の評価に戻す。
規約：元の錐は任意。使われ方：反転表現可能比較の厳密な同定。 -/
lemma weightedConeComparison_reflected (W : I ⥤ SSet.{u}) {H : I ⥤ SSet.{u}}
    (c : Cone H) :
    SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeComparison (W ⋙ SSet.opFunctor) c) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedSectionsReflectedIso W H).hom =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeComparison W (SSet.opFunctor.mapCone c) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections_hom_ext
  intro i
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeComparison_π]
  apply uncurry_injective
  rw [uncurry_natural_left, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedSectionsReflectedIso_evaluation]
  change ((SSet.opFunctorCompOpFunctorIso.app (W.obj i)).inv ▷ c.pt.op) ≫
    (Functor.Monoidal.μIso SSet.opFunctor (W.obj i).op c.pt).hom ≫ SSet.opFunctor.map
      (((W.obj i).op ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeComparison (W ⋙ SSet.opFunctor) c) ≫
        uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsπ (W ⋙ SSet.opFunctor) H i)) =
    uncurry (curry (snd (W.obj i) c.pt.op ≫ SSet.opFunctor.map (c.π.app i)))
  rw [← uncurry_natural_left, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeComparison_π, uncurry_curry]
  rw [uncurry_curry, CategoryTheory.Functor.map_comp]
  rfl

end SerrePositivity.InfinityCategories.Project.FilteredExchange.WeightedConeOppositeComparison
