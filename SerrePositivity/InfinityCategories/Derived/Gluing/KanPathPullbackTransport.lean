module
public import SerrePositivity.InfinityCategories.Derived.Gluing.KanIntervalPathTransport
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.StrictKanPullbackMapEquivalence
public import SerrePositivity.InfinityCategories.F2.CatInfinity.KanTensorComplex

/-! 同じ二作用を係数同値で移す実 path 引き戻し比較は、同じ区間族を保つ同値。 -/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open HomotopicalAlgebra SSet.modelCategoryQuillen
open scoped _root_.Simplicial
variable {K L T : SSet.{u}} (f : K ⟶ L) (a : T ⟶ K ⊗ K)

lemma dgGluingKanPathPullback_kanComplex [KanComplex K] [KanComplex T] :
    KanComplex (pullback (F2.arrowEndpointPair K) a) := by
  let : Fibration (F2.arrowEndpointPair K) := dgGluingKanIntervalEndpointPair_fibration K
  exact HomotopyLimits.pullback_kanComplex_of_fibration _ _

def dgGluingKanPathPullbackTransport :
    pullback (F2.arrowEndpointPair K) a ⟶
      pullback (F2.arrowEndpointPair L) (a ≫ (f ⊗ₘ f)) :=
  pullback.map _ _ _ _ ((ihom (Δ[1] : SSet.{u})).map f) (𝟙 T) (f ⊗ₘ f)
    (dgGluingIntervalEndpointPair_naturality f) (by rw [Category.id_comp])

lemma dgGluingKanPathPullbackTransport_path :
    dgGluingKanPathPullbackTransport f a ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ (ihom (Δ[1] : SSet.{u})).map f :=
  pullback.lift_fst _ _ _

lemma dgGluingKanPathPullbackTransport_inputs :
    dgGluingKanPathPullbackTransport f a ≫ pullback.snd _ _ = pullback.snd _ _ := by
  exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)

lemma dgGluingKanPathPullbackTransport_equivalence [KanComplex K] [KanComplex L]
    [KanComplex T] (hf : IsSimplicialHomotopyEquivalence f) :
    IsSimplicialHomotopyEquivalence (dgGluingKanPathPullbackTransport f a) := by
  let : KanComplex (K ⊗ K) := F2.kanComplex_tensor _ _
  let : KanComplex (L ⊗ L) := F2.kanComplex_tensor _ _
  let : Fibration (F2.arrowEndpointPair K) := dgGluingKanIntervalEndpointPair_fibration K
  let : Fibration (F2.arrowEndpointPair L) := dgGluingKanIntervalEndpointPair_fibration L
  exact F2.strictKanPullbackMap_homotopyEquivalence _ _ _ _ _ _ _
    (dgGluingIntervalEndpointPair_naturality f) (by rw [Category.id_comp])
    (dgGluingIntervalMap_homotopyEquivalence hf) (isSimplicialHomotopyEquivalence_id _)
    (dgGluingProductMap_homotopyEquivalence hf hf)

end SerrePositivity.InfinityCategories
