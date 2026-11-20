module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Generators
public import SerrePositivity.HomotopicalAlgebra.Simplicial.Generators
public import SerrePositivity.Spectra.PointedSimplicialSet.Spheres
public import SerrePositivity.HomotopicalAlgebra.Under.ModelCategory

/-! # Cofibrancy of the actual pointed simplicial sets and circle

Only the fixed monomorphism cofibration class is used. No weak-equivalence
class or completed Kan-Quillen model structure is assumed.
-/

@[expose] public section
universe u
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen
namespace SerrePositivity.SimplicialModelInputs

lemma pointed_basepoint_mono (X : PointedSimplicialSet.{u}) : Mono X.hom := by
  have : ∀ n, Mono (X.hom.app n) := by
    intro n
    apply (CategoryTheory.mono_iff_injective (X.hom.app n)).2
    intro a b _
    change (a : PUnit.{u + 1}) = b
    exact @Subsingleton.elim PUnit.{u + 1} inferInstance a b
  exact NatTrans.mono_of_mono_app X.hom

/-- All existing pointed simplicial sets are cofibrant for the Under mono class. -/
lemma pointedSimplicialSet_isCofibrant (X : PointedSimplicialSet.{u}) : IsCofibrant X := by
  let : (cofibrations PointedSimplicialSet.{u}).RespectsIso := by
    rw [cofibrations_under_def, MorphismProperty.under_eq_inverseImage]
    change ((MorphismProperty.monomorphisms SSet.{u}).inverseImage
      (Under.forget (𝟙_ SSet.{u}))).RespectsIso
    infer_instance
  apply (isCofibrant_iff_of_isInitial (PointedObject.fromPoint X)
    PointedObject.point_isZero.isInitial).2
  apply (cofibrations_under_iff _ _).2
  have := pointed_basepoint_mono X
  exact SSet.modelCategoryQuillen.cofibration_of_mono X.hom

lemma circle_isCofibrant : IsCofibrant PointedSimplicialSet.circle.{u} :=
  pointedSimplicialSet_isCofibrant _

end SerrePositivity.SimplicialModelInputs
