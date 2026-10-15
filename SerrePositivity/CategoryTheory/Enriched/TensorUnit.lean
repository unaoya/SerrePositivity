module

public import SerrePositivity.CategoryTheory.Enriched.TensorCotensor
public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas

/-! # The represented enriched tensor unit is naturally the identity -/

@[expose] public section
universe u v u' v'
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory

namespace SerrePositivity.Enriched
variable {V : Type u} [Category.{v} V] [MonoidalCategory V]
  {C : Type u'} [Category.{v'} C] [EnrichedOrdinaryCategory V C]

lemma eHomEquiv_postcomp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    eHomEquiv V (f ≫ g) = eHomEquiv V f ≫ eHomWhiskerLeft V X g := by
  rw [eHomEquiv_comp, unitors_inv_equal, rightUnitor_inv_comp_tensorHom_assoc]
  rfl

lemma eHomEquiv_precomp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    eHomEquiv V (f ≫ g) = eHomEquiv V g ≫ eHomWhiskerRight V f Z := by
  rw [eHomEquiv_comp, leftUnitor_inv_comp_tensorHom_assoc]
  rfl

namespace TensorCotensor
variable (S : TensorCotensor V C)

def unitMap (X : C) : (S.tensor.obj (𝟙_ V)).obj X ⟶ X :=
  (S.tensorHomEquiv (𝟙_ V) X X).symm (eHomEquiv V (𝟙 X))

lemma unitMap_comp {X Y : C} (f : X ⟶ Y) :
    unitMap S X ≫ f = (S.tensorHomEquiv (𝟙_ V) X Y).symm (eHomEquiv V f) := by
  apply (S.tensorHomEquiv (𝟙_ V) X Y).injective
  rw [S.tensorHom_naturality_target, unitMap, Equiv.apply_symm_apply,
    ← eHomEquiv_postcomp, Category.id_comp, Equiv.apply_symm_apply]

instance unitMap_isIso (X : C) : IsIso (unitMap S X) := by
  apply isIso_of_coyoneda_map_bijective
  intro Y
  let E : (X ⟶ Y) ≃ ((S.tensor.obj (𝟙_ V)).obj X ⟶ Y) :=
    (eHomEquiv V).trans (S.tensorHomEquiv (𝟙_ V) X Y).symm
  have h : (fun f : X ⟶ Y ↦ unitMap S X ≫ f) = E := by
    funext f
    exact unitMap_comp S f
  exact h.symm ▸ E.bijective

lemma unitMap_naturality {X Y : C} (f : X ⟶ Y) :
    (S.tensor.obj (𝟙_ V)).map f ≫ unitMap S Y = unitMap S X ≫ f := by
  apply (S.tensorHomEquiv (𝟙_ V) X Y).injective
  rw [S.tensorHom_naturality_source, unitMap, Equiv.apply_symm_apply,
    ← eHomEquiv_precomp, Category.comp_id, unitMap_comp, Equiv.apply_symm_apply]

def unitIso : S.tensor.obj (𝟙_ V) ≅ 𝟭 C :=
  NatIso.ofComponents (fun X ↦ by
    let e := asIso (unitMap S X)
    exact e) (fun {_ _} f ↦ unitMap_naturality S f)

end TensorCotensor
end SerrePositivity.Enriched
