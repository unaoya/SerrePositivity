module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalFunctorHomPrismCurry
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ParameterizedSquare
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorTriangleSquare

/-! 矢印圏の実区間 Hom を、共通対角を持つ二つの全パラメーター三角形へ分ける。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
variable {T X : SSet.{u}} (F G : (Δ[1] : SSet.{u}) ⟶ X)

structure DGGluingArrowHomTrianglePair where
  first : (Δ[2] : SSet.{u}) ⊗ T ⟶ X
  second : (Δ[2] : SSet.{u}) ⊗ T ⟶ X
  diagonal : (stdSimplex.δ (1 : Fin 3) ▷ T) ≫ first =
    (stdSimplex.δ (1 : Fin 3) ▷ T) ≫ second
  source : (stdSimplex.δ (2 : Fin 3) ▷ T) ≫ first = fst Δ[1] T ≫ F
  target : (stdSimplex.δ (0 : Fin 3) ▷ T) ≫ second = fst Δ[1] T ≫ G

@[ext] lemma DGGluingArrowHomTrianglePair.ext
    {a b : DGGluingArrowHomTrianglePair (T := T) F G}
    (hfirst : a.first = b.first) (hsecond : a.second = b.second) : a = b := by
  cases a
  cases b
  cases hfirst
  cases hsecond
  rfl

def dgGluingArrowHomTrianglePairOfInterval
    (f : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G)) :
    DGGluingArrowHomTrianglePair (T := T) F G where
  first := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 ▷ T) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalFunctorHomPrism f
  second := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ▷ T) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalFunctorHomPrism f
  diagonal := by
    simp only [← Category.assoc, ← comp_whiskerRight, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle_diagonal]
  source := by
    rw [← Category.assoc, ← comp_whiskerRight, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.triangleSquare_upper_left]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalFunctorHomPrism_zero f
  target := by
    rw [← Category.assoc, ← comp_whiskerRight, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.triangleSquare_lower_right]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalFunctorHomPrism_one f

lemma dgGluingArrowHomTrianglePairOfInterval_injective :
    Function.Injective (dgGluingArrowHomTrianglePairOfInterval (T := T) F G) := by
  intro f g h
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalFunctorHomPrism_injective F G
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.parameterizedSquare_hom_ext
  · exact congrArg DGGluingArrowHomTrianglePair.first h
  · exact congrArg DGGluingArrowHomTrianglePair.second h

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
