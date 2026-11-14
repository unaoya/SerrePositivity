module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.ArrowHomotopies.ArrowHomTriangleCurry

/-! 二合成三角形の厳密な表示は、任意の高次パラメーターの引き戻しと可換。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
variable {S T X : SSet.{u}} {F G : (Δ[1] : SSet.{u}) ⟶ X}

def dgGluingArrowHomTriangleReindex (k : S ⟶ T)
    (a : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingArrowHomTrianglePair (T := T) F G) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingArrowHomTrianglePair (T := S) F G where
  first := (Δ[2] ◁ k) ≫ a.first
  second := (Δ[2] ◁ k) ≫ a.second
  diagonal := by
    change (Δ[1] ◁ k) ≫ ((stdSimplex.δ (1 : Fin 3) ▷ T) ≫ a.first) =
      (Δ[1] ◁ k) ≫ ((stdSimplex.δ (1 : Fin 3) ▷ T) ≫ a.second)
    rw [a.diagonal]
  source := by
    change (Δ[1] ◁ k) ≫ ((stdSimplex.δ (2 : Fin 3) ▷ T) ≫ a.first) = _
    rw [a.source]
    rfl
  target := by
    change (Δ[1] ◁ k) ≫ ((stdSimplex.δ (0 : Fin 3) ▷ T) ≫ a.second) = _
    rw [a.target]
    rfl

lemma dgGluingArrowHomPrism_precomp (k : S ⟶ T)
    (f : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalFunctorHomPrism (k ≫ f) =
      ((Δ[1] ⊗ Δ[1]) ◁ k) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalFunctorHomPrism f := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalFunctorHomPrism
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp]
  rfl

lemma dgGluingArrowHomTriangles_naturality (k : S ⟶ T)
    (f : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G)) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingArrowHomTrianglePairOfInterval F G (k ≫ f) =
      dgGluingArrowHomTriangleReindex k (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingArrowHomTrianglePairOfInterval F G f) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingArrowHomTrianglePair.ext
  · change (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 ▷ S) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalFunctorHomPrism (k ≫ f) = _
    rw [dgGluingArrowHomPrism_precomp]
    rfl
  · change (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ▷ S) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalFunctorHomPrism (k ≫ f) = _
    rw [dgGluingArrowHomPrism_precomp]
    rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
