module

public import SerrePositivity.Spectra.Pointed.SmashMonoidal
public import SerrePositivity.HomotopicalAlgebra.Under.ModelCategory
public import SerrePositivity.HomotopicalAlgebra.Monoidal.CofibrantTensor

/-! # The model structure on the existing pointed objects

The three classes are those of the Under model. Cofibrancy means that the
basepoint map is a cofibration. Free basepoint addition is left Quillen, and
sends a cofibrant cartesian unit to the actual smash unit.
-/

@[expose] public section
universe v u
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
namespace SerrePositivity.PointedModel
open SerrePositivity.PointedObject SerrePositivity.Quillen
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [ModelCategory C]

lemma cofibration_iff_underlying {X Y : PointedObject C} (f : X ⟶ Y) :
    Cofibration f ↔ Cofibration f.right := cofibrations_under_iff _ f

lemma fibration_iff_underlying {X Y : PointedObject C} (f : X ⟶ Y) :
    Fibration f ↔ Fibration f.right := fibrations_under_iff _ f

lemma weakEquivalence_iff_underlying {X Y : PointedObject C} (f : X ⟶ Y) :
    WeakEquivalence f ↔ WeakEquivalence f.right := weakEquivalences_under_iff _ f

/-- Pointed cofibrancy is the basepoint cofibration condition. -/
lemma isCofibrant_iff_basepoint (X : PointedObject C) :
    IsCofibrant X ↔ Cofibration X.hom := by
  rw [isCofibrant_iff_of_isInitial (fromPoint X) point_isZero.isInitial,
    cofibration_iff_underlying]
  rfl

lemma forget_isRightQuillen : IsRightQuillen (forget (C := C)) := by
  constructor
  · intro X Y f hf
    exact hf
  · intro X Y f hf
    exact hf

/-- The existing free-basepoint adjunction is Quillen for the Under model. -/
lemma adjoin_isLeftQuillen : IsLeftQuillen (adjoinFunctor (C := C)) := by
  have := forget_isRightQuillen (C := C)
  exact isLeftQuillen_of_isRightQuillen adjoinForgetAdjunction

lemma adjoin_isCofibrant (X : C) [IsCofibrant X] : IsCofibrant (adjoin X) := by
  let : (adjoinFunctor (C := C)).IsLeftAdjoint := adjoinForgetAdjunction.isLeftAdjoint
  have := adjoin_isLeftQuillen (C := C)
  exact map_isCofibrant adjoinFunctor X

/-- The zero-sphere is cofibrant when the cartesian unit is cofibrant. -/
lemma sphereZero_isCofibrant [IsCofibrant (𝟙_ C)] :
    IsCofibrant (sphereZero (C := C)) := adjoin_isCofibrant (𝟙_ C)

/-- Cofibrancy of the actual unit of the existing smash monoidal structure. -/
lemma smashUnit_isCofibrant [MonoidalClosed C] [IsCofibrant (𝟙_ C)] :
    IsCofibrant (𝟙_ (PointedObject C)) := sphereZero_isCofibrant

/-- The actual smash structure satisfies the separate unit axiom. -/
lemma smash_hasUnitAxiom [MonoidalClosed C] [IsCofibrant (𝟙_ C)] :
    HasUnitAxiom (PointedObject C) := by
  have := smashUnit_isCofibrant (C := C)
  exact unitAxiom_of_cofibrant_unit (PointedObject C)

end SerrePositivity.PointedModel
