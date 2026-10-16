module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanLocalizedCoproducts
public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanLocalizedTransfinite
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.ClosedObjectwise
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.SimplexFinite
public import SerrePositivity.HomotopicalAlgebra.Smith.AccessibleLimits
public import Mathlib.CategoryTheory.Presentable.Type

/-! # Reedy localized mono equivalences are precisely Reedy monos with localized components -/

@[expose] public section
universe v
noncomputable section
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.Reedy

namespace SerrePositivity.SimplicialModel.LocalizedMonoReedy
open KanTestLiftingClass

local instance : IsLocallyPresentable.{v} SSet.{v} :=
  Smith.AccessibleLimits.functorCategory_isLocallyPresentable
    (C := Type v) SimplexCategoryᵒᵖ

instance multiplicative : localizedMonos.{v}.IsMultiplicative := by
  rw [localizedMonos_eq]
  infer_instance

instance retracts : localizedMonos.{v}.IsStableUnderRetracts := by
  rw [localizedMonos_eq]
  infer_instance

instance coproducts : localizedMonos.{v}.IsStableUnderCoproducts.{v} := by
  constructor
  intro I
  apply MorphismProperty.IsStableUnderCoproductsOfShape.mk
  intro A B _ _ f hf
  have : ∀ i, Mono (f i) := fun i => (hf i).1
  have hl := KanLocalizedCoproducts.coproduct_mem rightTests.llp I f
    (fun i => localizedMono_le_llp _ (hf i))
  exact ⟨inferInstance, localized_isIso_of_llp _ hl⟩

instance cobaseChange : localizedMonos.{v}.IsStableUnderCobaseChange := by
  rw [localizedMonos_eq]
  infer_instance

abbrev equivalences : MorphismProperty SSet.{v} :=
  (MorphismProperty.isomorphisms _).inverseImage AnodyneHomotopy.anodyneQ

lemma localizedMonos_inf : localizedMonos.{v} =
    MorphismProperty.monomorphisms SSet.{v} ⊓ equivalences := rfl

lemma reedy_iff {A B : SimplexCategoryᵒᵖ ⥤ SSet.{v}} (f : A ⟶ B) :
    reedyLeft simplexOp localizedMonos f ↔
      reedyLeft simplexOp (MorphismProperty.monomorphisms _) f ∧
        ∀ n, IsIso (AnodyneHomotopy.anodyneQ.map (f.app n)) := by
  have : (MorphismProperty.monomorphisms SSet.{v} ⊓ equivalences).IsMultiplicative :=
    multiplicative
  have : (MorphismProperty.monomorphisms SSet.{v} ⊓ equivalences).IsStableUnderRetracts := retracts
  have : (MorphismProperty.monomorphisms SSet.{v} ⊓ equivalences).IsStableUnderCoproducts.{v} :=
    coproducts
  have : (MorphismProperty.monomorphisms SSet.{v} ⊓ equivalences).IsStableUnderCobaseChange :=
    cobaseChange
  have : MorphismProperty.IsStableUnderTransfiniteComposition.{v}
      (MorphismProperty.monomorphisms SSet.{v} ⊓ equivalences) := KanLocalizedTransfinite.stable
  rw [localizedMonos_inf]
  exact reedyLeft_inf_iff.{v} simplexOp f (MorphismProperty.monomorphisms _) equivalences

end SerrePositivity.SimplicialModel.LocalizedMonoReedy
