module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.CategoryTheory.Enriched.TensorCotensor
public import SerrePositivity.HomotopicalAlgebra.Monoidal.QuillenBifunctor

/-!
# Model compatibility for represented tensor/cotensor data

All statements are over an arbitrary enriching model category V. They do not
require or construct a simplicial enrichment for a dg category. The ordinary
adjoints supplied by the representability data give one-variable Quillen
functors after fixing cofibrant parameters.
-/

@[expose] public section

universe u v u' v'

open CategoryTheory HomotopicalAlgebra SerrePositivity.Quillen

namespace SerrePositivity.Enriched

variable {V : Type u} [Category.{v} V] [MonoidalCategory V] [ModelCategory V]
  {C : Type u'} [Category.{v'} C] [ModelCategory C] [EnrichedOrdinaryCategory V C]
  (S : TensorCotensor V C)

/-- Tensor compatibility is equivalent to the cotensor pullback-power criterion. -/
theorem tensor_iff_cotensor_model :
    IsQuillenBifunctor S.tensor ↔ HasQuillenPullbackHom S.cotensor :=
  isQuillenBifunctor_iff_pullbackHom S.tensorCotensor

/-- The same compatibility is equivalent to the enriched mapping pullback-hom
criterion, the general receiver for SM7. -/
theorem tensor_iff_mapping_model :
    IsQuillenBifunctor S.tensor ↔ HasQuillenPullbackHom (eHomFunctor V C) := by
  rw [← isQuillenBifunctor_flip_iff S.tensor]
  exact isQuillenBifunctor_iff_pullbackHom S.tensorHom

variable [IsQuillenBifunctor S.tensor]

lemma tensor_isLeftQuillen (K : V) [IsCofibrant K] : IsLeftQuillen (S.tensor.obj K) := by
  have : ∀ X : C, (S.tensor.flip.obj X).IsLeftAdjoint :=
    fun X ↦ (S.tensorHom.adj X).isLeftAdjoint
  exact isLeftQuillen_obj_of_cofibrant S.tensor K

lemma cotensor_isRightQuillen (K : V) [IsCofibrant K] :
    IsRightQuillen (S.cotensor.obj (Opposite.op K)) := by
  have := tensor_isLeftQuillen S K
  exact isRightQuillen_of_isLeftQuillen (S.tensorCotensor.adj K)

lemma tensor_parameter_isLeftQuillen (X : C) [IsCofibrant X] :
    IsLeftQuillen (S.tensor.flip.obj X) := by
  have : ∀ K : V, (S.tensor.flip.flip.obj K).IsLeftAdjoint :=
    fun K ↦ (S.tensorCotensor.adj K).isLeftAdjoint
  exact isLeftQuillen_obj_of_cofibrant S.tensor.flip X

include S in
lemma mapping_isRightQuillen (X : C) [IsCofibrant X] :
    IsRightQuillen ((eHomFunctor V C).obj (Opposite.op X)) := by
  have := tensor_parameter_isLeftQuillen S X
  exact isRightQuillen_of_isLeftQuillen (S.tensorHom.adj X)

end SerrePositivity.Enriched

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "A.3.1.6"] _root_.SerrePositivity.Enriched.tensor_iff_cotensor_model
attribute [cite HTT "A.3.1.6"] _root_.SerrePositivity.Enriched.tensor_iff_mapping_model
