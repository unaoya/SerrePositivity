module
public import SerrePositivity.InfinityCategories.Derived.Gluing.IntervalPathPullbackCoordinates
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.IntervalReplacementPathSection
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.StrictKanPullbackMapEquivalence
public import SerrePositivity.InfinityCategories.F1B.Homotopy.WeakWhitehead

/-! 一脚が fibration の厳密引き戻しから、同じ定値 path の区間引き戻しへの比較。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open HomotopicalAlgebra SSet.modelCategoryQuillen
variable {A B Q : SSet.{u}} [KanComplex Q]
  (f : A ⟶ Q) (g : B ⟶ Q)

def dgGluingStrictIntervalPullbackComparison : pullback f g ⟶ F2.intervalPullback f g :=
  pullback.map f g (F2.intervalReplacementEndpoint f) g
    (F2.intervalReplacementSection f) (𝟙 B) (𝟙 Q)
    (by rw [Category.comp_id, F2.intervalReplacementSection_endpoint])
    (by simp only [Category.comp_id, Category.id_comp])

lemma dgGluingStrictIntervalPullbackComparison_equivalence
    [KanComplex A] [KanComplex B] [Fibration f] :
    IsSimplicialHomotopyEquivalence (dgGluingStrictIntervalPullbackComparison f g) := by
  apply F2.strictKanPullbackMap_homotopyEquivalence f g (F2.intervalReplacementEndpoint f) g
    (F2.intervalReplacementSection f) (𝟙 B) (𝟙 Q)
    (by rw [Category.comp_id, F2.intervalReplacementSection_endpoint])
    (by simp only [Category.comp_id, Category.id_comp])
  · have hh := F2.intervalReplacementSection_isWeakHomotopyEquivalence f
    exact hh.isSimplicialHomotopyEquivalence
  · exact isSimplicialHomotopyEquivalence_id B
  · exact isSimplicialHomotopyEquivalence_id Q

lemma dgGluingStrictIntervalPullbackComparison_path :
    dgGluingStrictIntervalPullbackComparison f g ≫ F2.intervalPullbackPath f g =
      pullback.fst f g ≫ f ≫ dgGluingConstantIntervalPath Q := by
  simp only [dgGluingStrictIntervalPullbackComparison, F2.intervalPullbackPath,
    pullback.map, pullback.lift_fst_assoc, Category.assoc,
    F2.intervalReplacementSection_path, dgGluingConstantIntervalPath, equivalencePathRefl_ι]

lemma dgGluingStrictIntervalPullbackComparison_left :
    dgGluingStrictIntervalPullbackComparison f g ≫ F2.intervalPullbackLeft f g =
      pullback.fst f g := by
  simp only [dgGluingStrictIntervalPullbackComparison, F2.intervalPullbackLeft,
    pullback.map, pullback.lift_fst_assoc, Category.assoc,
    F2.intervalReplacementSection_projection, Category.comp_id]

lemma dgGluingStrictIntervalPullbackComparison_right :
    dgGluingStrictIntervalPullbackComparison f g ≫ F2.intervalPullbackRight f g =
      pullback.snd f g := by
  simp only [dgGluingStrictIntervalPullbackComparison, F2.intervalPullbackRight,
    pullback.map, pullback.lift_snd, Category.comp_id]

end SerrePositivity.InfinityCategories
