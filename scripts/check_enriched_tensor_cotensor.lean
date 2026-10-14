import SerrePositivity.HomotopicalAlgebra.Foundations

universe u v u' v'
open CategoryTheory HomotopicalAlgebra Opposite
open SerrePositivity.Enriched SerrePositivity.Quillen

variable {V : Type u} [Category.{v} V] [MonoidalCategory V]
  {C : Type u'} [Category.{v'} C] [EnrichedOrdinaryCategory V C]
  (S : TensorCotensor V C)

example (K : V) (X Y : C) (f : (S.tensor.obj K).obj X ⟶ Y) :
    S.cotensorHomEquiv K X Y (S.tensorCotensorHomEquiv K X Y f) =
      S.tensorHomEquiv K X Y f := S.homEquiv_compatibility K X Y f

example {K L : V} (a : K ⟶ L) (X Y : C)
    (f : X ⟶ (S.cotensor.obj (op L)).obj Y) :
    S.cotensorHomEquiv K X Y (f ≫ (S.cotensor.map a.op).app Y) =
      a ≫ S.cotensorHomEquiv L X Y f := S.cotensorHom_naturality_parameter a X Y f

example (K : V) (X : C) :
    (S.tensor.obj K).map (S.coevaluation K X) ≫ S.evaluation K ((S.tensor.obj K).obj X) =
      𝟙 _ := S.tensor_triangle K X

example [MonoidalClosed V] (E : EnrichedRepresentability S) (K : V) (X Y : C)
    (f : (S.tensor.obj K).obj X ⟶ Y) :
    eHomEquiv V f ≫ (E.homObjectComparison K X Y).hom =
      eHomEquiv V (S.tensorCotensorHomEquiv K X Y f) :=
  E.homObjectComparison_points K X Y f

section Model
variable [ModelCategory V] [ModelCategory C]

example : IsQuillenBifunctor S.tensor ↔ HasQuillenPullbackHom S.cotensor :=
  tensor_iff_cotensor_model S

example : IsQuillenBifunctor S.tensor ↔ HasQuillenPullbackHom (eHomFunctor V C) :=
  tensor_iff_mapping_model S

example [IsQuillenBifunctor S.tensor] (K : V) [IsCofibrant K] :
    IsLeftQuillen (S.tensor.obj K) ∧ IsRightQuillen (S.cotensor.obj (op K)) :=
  ⟨tensor_isLeftQuillen S K, cotensor_isRightQuillen S K⟩

example [IsQuillenBifunctor S.tensor] (X : C) [IsCofibrant X] :
    IsLeftQuillen (S.tensor.flip.obj X) ∧
      IsRightQuillen ((eHomFunctor V C).obj (op X)) :=
  ⟨tensor_parameter_isLeftQuillen S X, mapping_isRightQuillen S X⟩
end Model
