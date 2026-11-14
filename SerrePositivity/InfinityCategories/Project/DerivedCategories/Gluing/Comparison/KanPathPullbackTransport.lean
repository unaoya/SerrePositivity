module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Comparison.KanIntervalPathTransport
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.StrictKanPullbackMapEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanTensorComplex

/-! 同じ二作用を係数同値で移す実 path 引き戻し比較は、同じ区間族を保つ同値。 -/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open HomotopicalAlgebra SSet.modelCategoryQuillen
open scoped _root_.Simplicial
variable {K L T : SSet.{u}} (f : K ⟶ L) (a : T ⟶ K ⊗ K)

lemma dgGluingKanPathPullback_kanComplex [KanComplex K] [KanComplex T] :
    KanComplex (pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.arrowEndpointPair K) a) := by
  let : Fibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.arrowEndpointPair K) := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKanIntervalEndpointPair_fibration K
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.pullback_kanComplex_of_fibration _ _

def dgGluingKanPathPullbackTransport :
    pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.arrowEndpointPair K) a ⟶
      pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.arrowEndpointPair L) (a ≫ (f ⊗ₘ f)) :=
  pullback.map _ _ _ _ ((ihom (Δ[1] : SSet.{u})).map f) (𝟙 T) (f ⊗ₘ f)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIntervalEndpointPair_naturality f) (by rw [Category.id_comp])

lemma dgGluingKanPathPullbackTransport_path :
    dgGluingKanPathPullbackTransport f a ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ (ihom (Δ[1] : SSet.{u})).map f :=
  pullback.lift_fst _ _ _

lemma dgGluingKanPathPullbackTransport_inputs :
    dgGluingKanPathPullbackTransport f a ≫ pullback.snd _ _ = pullback.snd _ _ := by
  exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)

lemma dgGluingKanPathPullbackTransport_equivalence [KanComplex K] [KanComplex L]
    [KanComplex T] (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence f) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (dgGluingKanPathPullbackTransport f a) := by
  let : KanComplex (K ⊗ K) := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.kanComplex_tensor _ _
  let : KanComplex (L ⊗ L) := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.kanComplex_tensor _ _
  let : Fibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.arrowEndpointPair K) := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKanIntervalEndpointPair_fibration K
  let : Fibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.arrowEndpointPair L) := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKanIntervalEndpointPair_fibration L
  exact _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.strictKanPullbackMap_homotopyEquivalence _ _ _ _ _ _ _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIntervalEndpointPair_naturality f) (by rw [Category.id_comp])
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIntervalMap_homotopyEquivalence hf) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.isSimplicialHomotopyEquivalence_id _)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingProductMap_homotopyEquivalence hf hf)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
