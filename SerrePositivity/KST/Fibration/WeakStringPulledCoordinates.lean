module
public import SerrePositivity.KST.Fibration.WeakStringFinitePostNaturality
public import SerrePositivity.KST.Fibration.WeakStringFiniteKernelIso
public import SerrePositivity.KST.Fibration.WeakStringFiniteAllLengths

/-! # 元の後合成に沿って引き戻した cofiber 座標と初期評価 -/

@[expose] public section
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration

/-- 初期成分を元の包含側に保ち、cofiber 成分だけを実際の後合成に沿って引き戻す。 -/
def weakStringPulledCoordinates {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (f : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (n r : ℕ) :=
  lift ((multiRealizationFunctor r).map
    (weakStringVertexTopExact (f ≫ q : A ⟶ C) ⦋n⦌ 0))
    ((multiRealizationFunctor r).map (weakStringPostExact f q ⦋n⦌) ≫
      weakStringConsecutiveCofibers q n r)

/-- 引き戻した実座標の局所化像は、元の有限比較と核係数の後合成の合成に等しい。 -/
theorem weakStringPulledCoordinates_localized_eq {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (f : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (n r : ℕ) :
    AnodyneHomotopy.anodyneQ.map (weakStringPulledCoordinates f q n (r + 1)) =
      AnodyneHomotopy.anodyneQ.map
        (weakStringFiniteComparison (f ≫ q : A ⟶ C) n (r + 1) ≫
          (_ ◁ Limits.Pi.map (fun _ : Fin n =>
            (multiRealizationFunctor (r + 1)).map (kernelPostExact f q)))) := by
  unfold weakStringPulledCoordinates weakStringFiniteComparison
  rw [lift_whiskerLeft]
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pair_eq_of_anodyneQ_eq rfl
  apply finProduct_eq_of_anodyneQ_eq
  intro j
  simpa only [weakStringConsecutiveCofibers, Category.assoc, Limits.Pi.map_π,
    Pi.lift_comp_π_assoc, Pi.lift_comp_π, Functor.map_comp] using
    weakStringCofiberMultiMap_postcomp f q (consecutiveWeakStringEdge n j) r

/-- Verdier 列では、元の引き戻した座標射自体が全長・全正反復で局所化同型。 -/
theorem weakStringPulledCoordinates_verdier_localized_isIso
    {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
    (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) (n r : ℕ) :
    IsIso (AnodyneHomotopy.anodyneQ.map (weakStringPulledCoordinates i q n (r + 1))) := by
  rw [weakStringPulledCoordinates_localized_eq, Functor.map_comp]
  have := weakStringFiniteComparison_localized_isIso (i ≫ q : A ⟶ C) n r
  have hk := weakStringFiniteKernelPostMap_verdier_localized_isIso h n r
  have := AnodyneHomotopy.whiskerLeft_anodyneQ_isIso _ hk
    ((multiRealizationFunctor (r + 1)).obj
      (closedStableModel (ClosedStablePredicate.top (sInputModel A))))
  infer_instance

end SerrePositivity.KST.Fibration
