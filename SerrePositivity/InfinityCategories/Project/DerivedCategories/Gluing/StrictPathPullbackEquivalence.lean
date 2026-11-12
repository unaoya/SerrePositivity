module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.StrictIntervalPullbackComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanTensorComplex

/-! 前に構成した定値全 path 比較そのものは、一脚が Kan fibration なら同値。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
variable {A B Q : SSet.{u}} [KanComplex Q] (f : A ⟶ Q) (g : B ⟶ Q)

lemma dgGluingStrictPathPullbackMap_factor :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStrictPathPullbackMap f g =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStrictIntervalPullbackComparison f g ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIntervalPathCoordinatesIso f g).hom := by
  apply pullback.hom_ext
  · rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStrictPathPullbackMap_path, Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIntervalPathCoordinatesIso_path, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStrictIntervalPullbackComparison_path]
  · rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStrictPathPullbackMap_inputs, Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIntervalPathCoordinatesIso_inputs]
    apply CartesianMonoidalCategory.hom_ext
    · simp only [_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackInputPair, Category.assoc, lift_fst]
      exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStrictIntervalPullbackComparison_left f g).symm
    · simp only [_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackInputPair, Category.assoc, lift_snd]
      exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStrictIntervalPullbackComparison_right f g).symm

omit [KanComplex Q] in
lemma dgGluingKanPullback_of_leftFibration {L M R : SSet.{u}}
    (p : L ⟶ M) (q : R ⟶ M) [KanComplex R] [Fibration p] :
    KanComplex (pullback p q) := by
  have : Fibration (pullback.snd p q) := by
    apply (SSet.modelCategoryQuillen.fibration_iff _).2
    exact J.rlp.pullback_snd _ _ ((SSet.modelCategoryQuillen.fibration_iff _).1
      (inferInstanceAs (Fibration p)))
  exact isFibrant_of_fibration (pullback.snd p q)

lemma dgGluingStrictPathPullbackMap_equivalence
    [KanComplex A] [KanComplex B] [Fibration f] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStrictPathPullbackMap f g) := by
  have := dgGluingKanPullback_of_leftFibration f g
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.kanComplex_tensor A B
  have := dgGluingKanPullback_of_leftFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.arrowEndpointPair Q) (f ⊗ₘ g)
  rw [dgGluingStrictPathPullbackMap_factor]
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStrictIntervalPullbackComparison_equivalence f g).comp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.homotopyEquivalence_of_isIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIntervalPathCoordinatesIso f g).hom)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
