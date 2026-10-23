module
public import SerrePositivity.InfinityCategories.Derived.Gluing.StrictIntervalPullbackComparison
public import SerrePositivity.InfinityCategories.F2.CatInfinity.KanTensorComplex

/-! 前に構成した定値全 path 比較そのものは、一脚が Kan fibration なら同値。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
variable {A B Q : SSet.{u}} [KanComplex Q] (f : A ⟶ Q) (g : B ⟶ Q)

lemma dgGluingStrictPathPullbackMap_factor :
    dgGluingStrictPathPullbackMap f g =
      dgGluingStrictIntervalPullbackComparison f g ≫
        (dgGluingIntervalPathCoordinatesIso f g).hom := by
  apply pullback.hom_ext
  · rw [dgGluingStrictPathPullbackMap_path, Category.assoc,
      dgGluingIntervalPathCoordinatesIso_path, dgGluingStrictIntervalPullbackComparison_path]
  · rw [dgGluingStrictPathPullbackMap_inputs, Category.assoc,
      dgGluingIntervalPathCoordinatesIso_inputs]
    apply CartesianMonoidalCategory.hom_ext
    · simp only [F2.intervalPullbackInputPair, Category.assoc, lift_fst]
      exact (dgGluingStrictIntervalPullbackComparison_left f g).symm
    · simp only [F2.intervalPullbackInputPair, Category.assoc, lift_snd]
      exact (dgGluingStrictIntervalPullbackComparison_right f g).symm

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
    IsSimplicialHomotopyEquivalence (dgGluingStrictPathPullbackMap f g) := by
  have := dgGluingKanPullback_of_leftFibration f g
  have := F2.kanComplex_tensor A B
  have := dgGluingKanPullback_of_leftFibration (F2.arrowEndpointPair Q) (f ⊗ₘ g)
  rw [dgGluingStrictPathPullbackMap_factor]
  exact (dgGluingStrictIntervalPullbackComparison_equivalence f g).comp
    (HomotopyLimits.homotopyEquivalence_of_isIso (dgGluingIntervalPathCoordinatesIso f g).hom)

end SerrePositivity.InfinityCategories
