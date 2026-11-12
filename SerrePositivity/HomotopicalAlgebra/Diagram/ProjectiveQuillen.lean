module

public import SerrePositivity.HomotopicalAlgebra.Diagram.Projective
public import SerrePositivity.HomotopicalAlgebra.Quillen.DerivedFunctor
public import Mathlib.CategoryTheory.Adjunction.Limits

/-! # Colimit as a left Quillen functor for the projective diagram model -/

@[expose] public section
universe w v u vH uH
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.DiagramModel.Projective
variable (K : Type w) [SmallCategory K] {C : Type u} [Category.{v} C]
  [ModelCategory C] [IsLocallyPresentable.{w} C]
  (I J : MorphismProperty C) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]

local instance : HasColimitsOfSize.{w, w} C := Smith.locallyPresentable_hasColimits (C := C)

lemma weakEquivalence_iff_objectwise {F G : K ⥤ C} (f : F ⟶ G) :
    let := modelCategory K I J
    WeakEquivalence f ↔ ∀ k, WeakEquivalence (f.app k) := by
  let := modelCategory K I J
  change WeakEquivalence f ↔ ∀ k, WeakEquivalence (f.app k)
  rw [weakEquivalence_iff]
  change (∀ k, weakEquivalences C (f.app k)) ↔ ∀ k, WeakEquivalence (f.app k)
  exact forall_congr' (fun k ↦ (weakEquivalence_iff (f.app k)).symm)

lemma fibration_iff_objectwise {F G : K ⥤ C} (f : F ⟶ G) :
    let := modelCategory K I J
    Fibration f ↔ ∀ k, Fibration (f.app k) := by
  let := modelCategory K I J
  change Fibration f ↔ ∀ k, Fibration (f.app k)
  rw [fibration_iff]
  change (∀ k, fibrations C (f.app k)) ↔ ∀ k, Fibration (f.app k)
  exact forall_congr' (fun k ↦ (fibration_iff (f.app k)).symm)

lemma evaluation_isRightQuillen (k : K) :
    let := modelCategory K I J
    Quillen.IsRightQuillen (evaluation K (C := C) k) := by
  let := modelCategory K I J
  exact ⟨fun _ _ _ hf ↦ hf k, fun _ _ _ hf ↦ ⟨hf.1 k, hf.2 k⟩⟩

lemma free_isLeftQuillen (k : K) :
    let := modelCategory K I J
    Quillen.IsLeftQuillen (free K (C := C) k) := by
  let := modelCategory K I J
  have := evaluation_isRightQuillen K I J k
  exact Quillen.isLeftQuillen_of_isRightQuillen (adjunction K k)

lemma constant_isRightQuillen :
    let := modelCategory K I J
    Quillen.IsRightQuillen (Functor.const K : C ⥤ K ⥤ C) := by
  let := modelCategory K I J
  exact ⟨fun _ _ _ hf _ ↦ hf, fun _ _ _ hf ↦ ⟨fun _ ↦ hf.1, fun _ ↦ hf.2⟩⟩

lemma colimit_isLeftQuillen :
    let := modelCategory K I J
    Quillen.IsLeftQuillen (colim : (K ⥤ C) ⥤ C) := by
  let := modelCategory K I J
  have := constant_isRightQuillen K I J
  exact Quillen.isLeftQuillen_of_isRightQuillen (colimConstAdj (J := K) (C := C))

lemma functorialFactorizations :
    let := modelCategory K I J
    (cofibrations (K ⥤ C)).HasFunctorialFactorization (trivialFibrations (K ⥤ C)) ∧
      (trivialCofibrations (K ⥤ C)).HasFunctorialFactorization (fibrations (K ⥤ C)) := by
  let := modelCategory K I J
  have := modelCategory_generated K I J
  exact ⟨_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.hasFunctorialFactorization_cofibration_trivialFibration
      (generators K I) (generators K J),
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.hasFunctorialFactorization_trivialCofibration_fibration
      (generators K I) (generators K J)⟩

/-- Colimit admits the actual Mathlib pointwise left derived functor for
every ordinary localization of the value category. -/
lemma hasPointwiseLeftDerivedColimit {H : Type uH} [Category.{vH} H]
    (L : C ⥤ H) [L.IsLocalization (weakEquivalences C)] :
    let := modelCategory K I J
    ((colim : (K ⥤ C) ⥤ C) ⋙ L).HasPointwiseLeftDerivedFunctor
      (weakEquivalences (K ⥤ C)) := by
  let := modelCategory K I J
  have := colimit_isLeftQuillen K I J
  infer_instance

end SerrePositivity.DiagramModel.Projective
