module

public import Mathlib.CategoryTheory.Enriched.Ordinary.Basic
public import Mathlib.CategoryTheory.Adjunction.Parametrized

/-!
# Represented tensor and cotensor for an existing enriched ordinary category

The mapping objects and their functoriality are Mathlib's `eHomFunctor`.
Two existing parametrized adjunctions express tensor/mapping and tensor/cotensor
representability. This supplies all three ordinary Hom equivalences, their
compatibility and naturality; the stronger enriched Hom-object representability
is kept separately in `EnrichedRepresentability`.
-/

@[expose] public section

universe u v u' v'

open CategoryTheory Opposite

namespace SerrePositivity.Enriched

variable (V : Type u) [Category.{v} V] [MonoidalCategory V]
  (C : Type u') [Category.{v'} C] [EnrichedOrdinaryCategory V C]

/-- Representability data on the existing enriched category, with no new
Hom object, ordinary category or adjunction type. -/
structure TensorCotensor where
  tensor : V ⥤ C ⥤ C
  cotensor : Vᵒᵖ ⥤ C ⥤ C
  tensorCotensor : tensor ⊣₂ cotensor
  tensorHom : tensor.flip ⊣₂ eHomFunctor V C

namespace TensorCotensor

variable {V C} (S : TensorCotensor V C)

def tensorHomEquiv (K : V) (X Y : C) :
    ((S.tensor.obj K).obj X ⟶ Y) ≃ (K ⟶ (X ⟶[V] Y)) :=
  (S.tensorHom.adj X).homEquiv K Y

def tensorCotensorHomEquiv (K : V) (X Y : C) :
    ((S.tensor.obj K).obj X ⟶ Y) ≃ (X ⟶ (S.cotensor.obj (op K)).obj Y) :=
  (S.tensorCotensor.adj K).homEquiv X Y

def cotensorHomEquiv (K : V) (X Y : C) :
    (X ⟶ (S.cotensor.obj (op K)).obj Y) ≃ (K ⟶ (X ⟶[V] Y)) :=
  (S.tensorCotensorHomEquiv K X Y).symm.trans (S.tensorHomEquiv K X Y)

lemma homEquiv_compatibility (K : V) (X Y : C) (f : (S.tensor.obj K).obj X ⟶ Y) :
    S.cotensorHomEquiv K X Y (S.tensorCotensorHomEquiv K X Y f) =
      S.tensorHomEquiv K X Y f := by
  simp [cotensorHomEquiv]

lemma tensorHom_naturality_parameter {K L : V} (a : K ⟶ L) (X Y : C)
    (f : (S.tensor.obj L).obj X ⟶ Y) :
    S.tensorHomEquiv K X Y ((S.tensor.map a).app X ≫ f) =
      a ≫ S.tensorHomEquiv L X Y f :=
  S.tensorHom.homEquiv_naturality_two a f

lemma tensorHom_naturality_source (K : V) {X X' : C} (a : X ⟶ X') (Y : C)
    (f : (S.tensor.obj K).obj X' ⟶ Y) :
    S.tensorHomEquiv K X Y ((S.tensor.obj K).map a ≫ f) =
      S.tensorHomEquiv K X' Y f ≫ eHomWhiskerRight V a Y :=
  S.tensorHom.homEquiv_naturality_one a f

lemma tensorHom_naturality_target (K : V) (X : C) {Y Y' : C} (b : Y ⟶ Y')
    (f : (S.tensor.obj K).obj X ⟶ Y) :
    S.tensorHomEquiv K X Y' (f ≫ b) =
      S.tensorHomEquiv K X Y f ≫ eHomWhiskerLeft V X b :=
  S.tensorHom.homEquiv_naturality_three b f

lemma tensorCotensor_naturality_parameter {K L : V} (a : K ⟶ L) (X Y : C)
    (f : (S.tensor.obj L).obj X ⟶ Y) :
    S.tensorCotensorHomEquiv K X Y ((S.tensor.map a).app X ≫ f) =
      S.tensorCotensorHomEquiv L X Y f ≫ (S.cotensor.map a.op).app Y :=
  S.tensorCotensor.homEquiv_naturality_one a f

lemma tensorCotensor_naturality_source (K : V) {X X' : C} (a : X ⟶ X') (Y : C)
    (f : (S.tensor.obj K).obj X' ⟶ Y) :
    S.tensorCotensorHomEquiv K X Y ((S.tensor.obj K).map a ≫ f) =
      a ≫ S.tensorCotensorHomEquiv K X' Y f :=
  S.tensorCotensor.homEquiv_naturality_two a f

lemma tensorCotensor_naturality_target (K : V) (X : C) {Y Y' : C} (b : Y ⟶ Y')
    (f : (S.tensor.obj K).obj X ⟶ Y) :
    S.tensorCotensorHomEquiv K X Y' (f ≫ b) =
      S.tensorCotensorHomEquiv K X Y f ≫ (S.cotensor.obj (op K)).map b :=
  S.tensorCotensor.homEquiv_naturality_three b f

lemma cotensorHom_naturality_parameter {K L : V} (a : K ⟶ L) (X Y : C)
    (f : X ⟶ (S.cotensor.obj (op L)).obj Y) :
    S.cotensorHomEquiv K X Y (f ≫ (S.cotensor.map a.op).app Y) =
      a ≫ S.cotensorHomEquiv L X Y f := by
  simp only [cotensorHomEquiv, tensorCotensorHomEquiv, Equiv.trans_apply]
  have h := S.tensorCotensor.homEquiv_symm_naturality_one a f
  change ((S.tensorCotensor.adj K).homEquiv X Y).symm
      (f ≫ (S.cotensor.map a.op).app Y) =
    (S.tensor.map a).app X ≫ ((S.tensorCotensor.adj L).homEquiv X Y).symm f at h
  rw [h, tensorHom_naturality_parameter]

lemma cotensorHom_naturality_source (K : V) {X X' : C} (a : X ⟶ X') (Y : C)
    (f : X' ⟶ (S.cotensor.obj (op K)).obj Y) :
    S.cotensorHomEquiv K X Y (a ≫ f) =
      S.cotensorHomEquiv K X' Y f ≫ eHomWhiskerRight V a Y := by
  simp only [cotensorHomEquiv, tensorCotensorHomEquiv, Equiv.trans_apply]
  have h := S.tensorCotensor.homEquiv_symm_naturality_two a f
  change ((S.tensorCotensor.adj K).homEquiv X Y).symm (a ≫ f) =
    (S.tensor.obj K).map a ≫ ((S.tensorCotensor.adj K).homEquiv X' Y).symm f at h
  rw [h, tensorHom_naturality_source]

lemma cotensorHom_naturality_target (K : V) (X : C) {Y Y' : C} (b : Y ⟶ Y')
    (f : X ⟶ (S.cotensor.obj (op K)).obj Y) :
    S.cotensorHomEquiv K X Y' (f ≫ (S.cotensor.obj (op K)).map b) =
      S.cotensorHomEquiv K X Y f ≫ eHomWhiskerLeft V X b := by
  simp only [cotensorHomEquiv, tensorCotensorHomEquiv, Equiv.trans_apply]
  have h := S.tensorCotensor.homEquiv_symm_naturality_three b f
  change ((S.tensorCotensor.adj K).homEquiv X Y').symm
      (f ≫ (S.cotensor.obj (op K)).map b) =
    ((S.tensorCotensor.adj K).homEquiv X Y).symm f ≫ b at h
  rw [h, tensorHom_naturality_target]

def evaluation (K : V) (Y : C) :
    (S.tensor.obj K).obj ((S.cotensor.obj (op K)).obj Y) ⟶ Y :=
  (S.tensorCotensor.adj K).counit.app Y

def coevaluation (K : V) (X : C) :
    X ⟶ (S.cotensor.obj (op K)).obj ((S.tensor.obj K).obj X) :=
  (S.tensorCotensor.adj K).unit.app X

lemma tensor_triangle (K : V) (X : C) :
    (S.tensor.obj K).map (S.coevaluation K X) ≫ S.evaluation K ((S.tensor.obj K).obj X) =
      𝟙 _ := (S.tensorCotensor.adj K).left_triangle_components X

lemma cotensor_triangle (K : V) (Y : C) :
    S.coevaluation K ((S.cotensor.obj (op K)).obj Y) ≫
      (S.cotensor.obj (op K)).map (S.evaluation K Y) = 𝟙 _ :=
  (S.tensorCotensor.adj K).right_triangle_components Y

end TensorCotensor

end SerrePositivity.Enriched
