module

public import SerrePositivity.CategoryTheory.Enriched.TensorCotensor
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-!
# Enriched Hom-object representability of tensor and cotensor

Ordinary Hom adjunctions alone do not assert an isomorphism of V-valued Hom
objects. This additional contract records those isomorphisms as natural
isomorphisms in both category variables, their variance in V, and compatibility
with the already chosen ordinary adjunctions. No new enrichment is constructed.
-/

@[expose] public section

universe u v u' v'

open CategoryTheory Opposite

namespace SerrePositivity.Enriched

variable {V : Type u} [Category.{v} V] [MonoidalCategory V] [MonoidalClosed V]
  {C : Type u'} [Category.{v'} C] [EnrichedOrdinaryCategory V C]
  (S : TensorCotensor V C)

def powerHom (K : V) : Cᵒᵖ ⥤ C ⥤ V :=
  eHomFunctor V C ⋙ (Functor.whiskeringRight C V V).obj (ihom K)

def tensorEnrichedHom (K : V) : Cᵒᵖ ⥤ C ⥤ V :=
  (S.tensor.obj K).op ⋙ eHomFunctor V C

def cotensorEnrichedHom (K : V) : Cᵒᵖ ⥤ C ⥤ V :=
  eHomFunctor V C ⋙ (Functor.whiskeringLeft C C V).obj (S.cotensor.obj (op K))

/-- Full V-valued representability, with all variance and the compatibility of
generalized points with the three ordinary Hom equivalences fixed explicitly. -/
structure EnrichedRepresentability where
  tensorIso (K : V) : tensorEnrichedHom S K ≅ powerHom (C := C) K
  cotensorIso (K : V) : cotensorEnrichedHom S K ≅ powerHom (C := C) K
  tensor_parameter {K L : V} (a : K ⟶ L) (X Y : C) :
    eHomWhiskerRight V ((S.tensor.map a).app X) Y ≫
        ((tensorIso K).hom.app (op X)).app Y =
      ((tensorIso L).hom.app (op X)).app Y ≫ (MonoidalClosed.pre a).app (X ⟶[V] Y)
  cotensor_parameter {K L : V} (a : K ⟶ L) (X Y : C) :
    eHomWhiskerLeft V X ((S.cotensor.map a.op).app Y) ≫
        ((cotensorIso K).hom.app (op X)).app Y =
      ((cotensorIso L).hom.app (op X)).app Y ≫ (MonoidalClosed.pre a).app (X ⟶[V] Y)
  tensor_points (K : V) (X Y : C) (f : (S.tensor.obj K).obj X ⟶ Y) :
    (MonoidalClosed.curryHomEquiv' (X := K) (Y := X ⟶[V] Y)).symm
      (eHomEquiv V f ≫ ((tensorIso K).hom.app (op X)).app Y) =
        S.tensorHomEquiv K X Y f
  cotensor_points (K : V) (X Y : C) (f : X ⟶ (S.cotensor.obj (op K)).obj Y) :
    (MonoidalClosed.curryHomEquiv' (X := K) (Y := X ⟶[V] Y)).symm
      (eHomEquiv V f ≫ ((cotensorIso K).hom.app (op X)).app Y) =
        S.cotensorHomEquiv K X Y f

namespace EnrichedRepresentability

variable {S} (E : EnrichedRepresentability S)

def tensorHomIso (K : V) (X Y : C) :
    ((S.tensor.obj K).obj X ⟶[V] Y) ≅ (ihom K).obj (X ⟶[V] Y) :=
  (E.tensorIso K).app (op X) |>.app Y

def cotensorHomIso (K : V) (X Y : C) :
    (X ⟶[V] (S.cotensor.obj (op K)).obj Y) ≅ (ihom K).obj (X ⟶[V] Y) :=
  (E.cotensorIso K).app (op X) |>.app Y

/-- The two representing Hom objects compare by their actual natural isomorphisms. -/
def homObjectComparison (K : V) (X Y : C) :
    ((S.tensor.obj K).obj X ⟶[V] Y) ≅ (X ⟶[V] (S.cotensor.obj (op K)).obj Y) :=
  E.tensorHomIso K X Y ≪≫ (E.cotensorHomIso K X Y).symm

/-- On ordinary points this enriched comparison is exactly the chosen
tensor/cotensor adjunction, rather than an unrelated isomorphism. -/
lemma homObjectComparison_points (K : V) (X Y : C)
    (f : (S.tensor.obj K).obj X ⟶ Y) :
    eHomEquiv V f ≫ (E.homObjectComparison K X Y).hom =
      eHomEquiv V (S.tensorCotensorHomEquiv K X Y f) := by
  apply (cancel_mono (E.cotensorHomIso K X Y).hom).1
  change (eHomEquiv V f ≫ (E.tensorHomIso K X Y).hom ≫
      (E.cotensorHomIso K X Y).inv) ≫ (E.cotensorHomIso K X Y).hom = _
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply (MonoidalClosed.curryHomEquiv' (X := K) (Y := X ⟶[V] Y)).symm.injective
  change (MonoidalClosed.curryHomEquiv' (X := K) (Y := X ⟶[V] Y)).symm
      (eHomEquiv V f ≫ ((E.tensorIso K).hom.app (op X)).app Y) =
    (MonoidalClosed.curryHomEquiv' (X := K) (Y := X ⟶[V] Y)).symm
      (eHomEquiv V (S.tensorCotensorHomEquiv K X Y f) ≫
        ((E.cotensorIso K).hom.app (op X)).app Y)
  rw [E.tensor_points, E.cotensor_points, S.homEquiv_compatibility]

end EnrichedRepresentability

end SerrePositivity.Enriched
