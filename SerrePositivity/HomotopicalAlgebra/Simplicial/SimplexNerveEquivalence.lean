module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.CellularNaturalComparison
public import SerrePositivity.HomotopicalAlgebra.Simplicial.SimplexNerveStandard
public import SerrePositivity.HomotopicalAlgebra.Simplicial.SimplexNerveMonos

/-! # The original simplex-nerve augmentation is inverted on every simplicial set

Standard simplices detect the natural comparison by actual cell pushouts
and the actual skeletal colimit. All value universes are allowed without
a model structure, cofinality hypothesis, or replacement augmentation.
-/

@[expose] public section
universe v uD vD
noncomputable section
open CategoryTheory

namespace SerrePositivity.SimplicialModel.SimplexNerve

lemma augmentation_localized_isIso (X : SSet.{v}) :
    IsIso (AnodyneHomotopy.anodyneQ.map (augmentation.app X)) :=
  CellularNaturalComparison.app_isIso augmentation
    (fun n => standardAugmentation_isIso AnodyneHomotopy.anodyneQ
      (Localization.inverts AnodyneHomotopy.anodyneQ SSet.anodyneExtensions) n) X

lemma map_localized_isIso {X Y : SSet.{v}} (f : X ⟶ Y)
    (hf : IsIso (AnodyneHomotopy.anodyneQ.map f)) :
    IsIso (AnodyneHomotopy.anodyneQ.map (functor.map f)) := by
  have : IsIso (AnodyneHomotopy.anodyneQ.map (augmentation.app X)) :=
    augmentation_localized_isIso X
  have : IsIso (AnodyneHomotopy.anodyneQ.map (augmentation.app Y)) :=
    augmentation_localized_isIso Y
  have : IsIso (AnodyneHomotopy.anodyneQ.map f) := hf
  have h := congrArg AnodyneHomotopy.anodyneQ.map (augmentation.naturality f)
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp] at h
  change AnodyneHomotopy.anodyneQ.map (functor.map f) ≫
    AnodyneHomotopy.anodyneQ.map (augmentation.app Y) =
      AnodyneHomotopy.anodyneQ.map (augmentation.app X) ≫ AnodyneHomotopy.anodyneQ.map f at h
  have hc : IsIso (AnodyneHomotopy.anodyneQ.map (functor.map f) ≫
      AnodyneHomotopy.anodyneQ.map (augmentation.app Y)) := h.symm ▸ inferInstance
  exact (isIso_comp_right_iff _ _).mp hc

variable {D : Type uD} [Category.{vD} D] (L : SSet.{v} ⥤ D)
  (hL : SSet.anodyneExtensions.IsInvertedBy L)

include hL in
lemma augmentation_image_isIso (X : SSet.{v}) : IsIso (L.map (augmentation.app X)) :=
  AnodyneHomotopy.map_isIso_of_anodyneQ_isIso L hL _ (augmentation_localized_isIso X)

include hL in
def augmentationImageIso : functor.{v} ⋙ L ≅ L :=
  NatIso.ofComponents (fun X => by
    have : IsIso (L.map (augmentation.app X)) := augmentation_image_isIso L hL X
    exact asIso (L.map (augmentation.app X))) (by
      intro X Y f
      change L.map (functor.map f) ≫ L.map (augmentation.app Y) =
        L.map (augmentation.app X) ≫ L.map f
      rw [← L.map_comp, ← L.map_comp, augmentation.naturality]
      rfl)

lemma augmentationImageIso_hom (X : SSet.{v}) :
    ((augmentationImageIso L hL).app X).hom = L.map (augmentation.app X) := rfl

end SerrePositivity.SimplicialModel.SimplexNerve
