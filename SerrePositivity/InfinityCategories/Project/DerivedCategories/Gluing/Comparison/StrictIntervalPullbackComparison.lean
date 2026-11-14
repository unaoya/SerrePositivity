module
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.IntervalReplacementKan
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ComparisonModels.IntervalPathPullbackCoordinates
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.IntervalReplacementPathSection
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.StrictKanPullbackMapEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.WeakWhitehead

/-! 一脚が fibration の厳密引き戻しから、同じ定値 path の区間引き戻しへの比較。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open HomotopicalAlgebra SSet.modelCategoryQuillen
variable {A B Q : SSet.{u}} [KanComplex Q]
  (f : A ⟶ Q) (g : B ⟶ Q)

def dgGluingStrictIntervalPullbackComparison : pullback f g ⟶ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullback f g :=
  pullback.map f g (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalReplacementEndpoint f) g
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalReplacementSection f) (𝟙 B) (𝟙 Q)
    (by rw [Category.comp_id, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalReplacementSection_endpoint])
    (by simp only [Category.comp_id, Category.id_comp])

lemma dgGluingStrictIntervalPullbackComparison_equivalence
    [KanComplex A] [KanComplex B] [Fibration f] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (dgGluingStrictIntervalPullbackComparison f g) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.strictKanPullbackMap_homotopyEquivalence f g (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalReplacementEndpoint f) g
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalReplacementSection f) (𝟙 B) (𝟙 Q)
    (by rw [Category.comp_id, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalReplacementSection_endpoint])
    (by simp only [Category.comp_id, Category.id_comp])
  · have hh := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalReplacementSection_isWeakHomotopyEquivalence f
    exact hh.isSimplicialHomotopyEquivalence
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.isSimplicialHomotopyEquivalence_id B
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.isSimplicialHomotopyEquivalence_id Q

lemma dgGluingStrictIntervalPullbackComparison_path :
    dgGluingStrictIntervalPullbackComparison f g ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackPath f g =
      pullback.fst f g ≫ f ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConstantIntervalPath Q := by
  simp only [dgGluingStrictIntervalPullbackComparison, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackPath,
    pullback.map, pullback.lift_fst_assoc, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalReplacementSection_path, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConstantIntervalPath, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.equivalencePathRefl_ι]

lemma dgGluingStrictIntervalPullbackComparison_left :
    dgGluingStrictIntervalPullbackComparison f g ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackLeft f g =
      pullback.fst f g := by
  simp only [dgGluingStrictIntervalPullbackComparison, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackLeft,
    pullback.map, pullback.lift_fst_assoc, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalReplacementSection_projection, Category.comp_id]

lemma dgGluingStrictIntervalPullbackComparison_right :
    dgGluingStrictIntervalPullbackComparison f g ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackRight f g =
      pullback.snd f g := by
  simp only [dgGluingStrictIntervalPullbackComparison, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackRight,
    pullback.map, pullback.lift_snd, Category.comp_id]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
