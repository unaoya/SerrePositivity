module
public import SerrePositivity.InfinityCategories.Derived.Gluing.ProductHomotopyEquivalence
public import SerrePositivity.InfinityCategories.F2.CatInfinity.ArrowEndpointPair
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.IntervalDiagram
public import SerrePositivity.InfinityCategories.Core.FunctorComposition
public import SerrePositivity.InfinityCategories.HomotopyLimits.KanEquivalencePaths

/-! Kan 係数空間の実区間族を、指定された係数写像で後合成する。 -/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open HomotopicalAlgebra SSet.modelCategoryQuillen
open scoped Simplicial

lemma dgGluingKanIntervalEndpointPair_fibration (K : SSet.{u}) [KanComplex K] :
    Fibration (F2.arrowEndpointPair K) := by
  rw [F2.arrowEndpointPair_restriction]
  apply (SSet.modelCategoryQuillen.fibration_iff _).2
  intro A B i hi
  let : HasLiftingProperty i ((pre F2.arrowBoundaryι).app K) :=
    (SSet.modelCategoryQuillen.fibration_iff _).1 inferInstance i hi
  infer_instance

lemma dgGluingIntervalEndpointPair_naturality {K L : SSet.{u}} (f : K ⟶ L) :
    F2.arrowEndpointPair K ≫ (f ⊗ₘ f) =
      (ihom (Δ[1] : SSet.{u})).map f ≫ F2.arrowEndpointPair L := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, F2.arrowEndpointPair, lift_fst, tensorHom_fst]
    exact (F2.intervalEndpointNatTrans 0).naturality f |>.symm
  · simp only [Category.assoc, F2.arrowEndpointPair, lift_snd, tensorHom_snd]
    exact (F2.intervalEndpointNatTrans 1).naturality f |>.symm

lemma dgGluingIntervalMap_homotopyEquivalence {K L : SSet.{u}}
    [KanComplex K] [KanComplex L] {f : K ⟶ L}
    (hf : IsSimplicialHomotopyEquivalence f) :
    IsSimplicialHomotopyEquivalence ((ihom (Δ[1] : SSet.{u})).map f) :=
  (hf.isQCatEquivalence.postcompose Δ[1]).isSimplicialHomotopyEquivalence

end SerrePositivity.InfinityCategories
