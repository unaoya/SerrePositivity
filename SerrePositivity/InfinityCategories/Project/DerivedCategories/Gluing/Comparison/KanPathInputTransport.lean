module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Comparison.KanPathPullbackTransport

/-! 指定された二端点を保つ入力同値は、同じ全 path の引き戻し比較を同値にする。 -/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open HomotopicalAlgebra SSet.modelCategoryQuillen
open scoped _root_.Simplicial
variable {Q T U : SSet.{u}} (a : T ⟶ Q ⊗ Q) (b : U ⟶ Q ⊗ Q)
  (s : T ⟶ U) (h : a = s ≫ b)

def dgGluingKanPathInputTransport :
    pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.arrowEndpointPair Q) a ⟶ pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.arrowEndpointPair Q) b :=
  pullback.map _ _ _ _ (𝟙 _) s (𝟙 _)
    (by simp only [Category.comp_id, Category.id_comp]) (by simpa only [Category.comp_id] using h)

lemma dgGluingKanPathInputTransport_path :
    dgGluingKanPathInputTransport a b s h ≫ pullback.fst _ _ = pullback.fst _ _ := by
  simp only [dgGluingKanPathInputTransport, pullback.map, pullback.lift_fst, Category.comp_id]

lemma dgGluingKanPathInputTransport_inputs :
    dgGluingKanPathInputTransport a b s h ≫ pullback.snd _ _ = pullback.snd _ _ ≫ s :=
  pullback.lift_snd _ _ _

lemma dgGluingKanPathInputTransport_equivalence
    [KanComplex Q] [KanComplex T] [KanComplex U]
    (hs : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence s) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (dgGluingKanPathInputTransport a b s h) := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.kanComplex_tensor Q Q
  have := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKanIntervalEndpointPair_fibration Q
  exact _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.strictKanPullbackMap_homotopyEquivalence _ _ _ _ _ _ _
    (by simp only [Category.comp_id, Category.id_comp])
    (by simpa only [Category.comp_id] using h)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.isSimplicialHomotopyEquivalence_id _) hs (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.isSimplicialHomotopyEquivalence_id _)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
