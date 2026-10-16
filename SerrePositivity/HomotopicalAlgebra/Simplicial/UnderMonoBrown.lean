module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.MonoLocalizedFactorization
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic

/-! # Brown's coproduct argument for mono objects under a simplicial set

A functor on the undercategory which inverts the localized mono maps
inverts all localized equivalences between objects with mono structure
maps. Boundary factorization replaces the model-category hypothesis.
-/

@[expose] public section
universe v uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.SimplicialModel.UnderMonoBrown
open MonoLocalizedFactorization
variable {A : SSet.{v}} {D : Type uD} [Category.{vD} D] (F : Under A ⥤ D)
  (hF : ∀ {X Y : Under A} (f : X ⟶ Y), Mono f.right →
    IsIso (AnodyneHomotopy.anodyneQ.map f.right) → IsIso (F.map f))

include hF in
lemma map_isIso {X Y : Under A} [Mono X.hom] [Mono Y.hom] (f : X ⟶ Y)
    (hf : IsIso (AnodyneHomotopy.anodyneQ.map f.right)) : IsIso (F.map f) := by
  let c := pushout.desc (f := X.hom) (g := Y.hom) f.right (𝟙 Y.right)
    (by rw [Category.comp_id]; exact f.w)
  let t := X.hom ≫ pushout.inl X.hom Y.hom ≫ left c
  let Z : Under A := Under.mk t
  let i : X ⟶ Z := Under.homMk (pushout.inl X.hom Y.hom ≫ left c) rfl
  let j : Y ⟶ Z := Under.homMk (pushout.inr X.hom Y.hom ≫ left c) (by
    change Y.hom ≫ pushout.inr X.hom Y.hom ≫ left c = t
    dsimp only [t]
    rw [← Category.assoc, ← pushout.condition, Category.assoc])
  let p : Z ⟶ Y := Under.homMk (right c) (by
    change (X.hom ≫ pushout.inl X.hom Y.hom ≫ left c) ≫ right c = Y.hom
    simp only [Category.assoc, fac]
    dsimp only [c]
    rw [pushout.inl_desc]
    exact f.w)
  have hip : i ≫ p = f := by
    ext1
    change (pushout.inl X.hom Y.hom ≫ left c) ≫ right c = f.right
    rw [Category.assoc, fac, pushout.inl_desc]
  have hjp : j ≫ p = 𝟙 Y := by
    ext1
    change (pushout.inr X.hom Y.hom ≫ left c) ≫ right c = 𝟙 Y.right
    rw [Category.assoc, fac, pushout.inr_desc]
  have hpr : IsIso (AnodyneHomotopy.anodyneQ.map p.right) := right_localized_isIso c
  have hi : IsIso (AnodyneHomotopy.anodyneQ.map i.right) := by
    have : IsIso (AnodyneHomotopy.anodyneQ.map p.right) := hpr
    have h := congrArg (fun k : X ⟶ Y => AnodyneHomotopy.anodyneQ.map k.right) hip
    change AnodyneHomotopy.anodyneQ.map (i.right ≫ p.right) = _ at h
    rw [CategoryTheory.Functor.map_comp] at h
    exact (isIso_comp_right_iff _ _).mp (h.symm ▸ hf)
  have hj : IsIso (AnodyneHomotopy.anodyneQ.map j.right) := by
    have : IsIso (AnodyneHomotopy.anodyneQ.map p.right) := hpr
    have h := congrArg (fun k : Y ⟶ Y => AnodyneHomotopy.anodyneQ.map k.right) hjp
    change AnodyneHomotopy.anodyneQ.map (j.right ≫ p.right) =
      AnodyneHomotopy.anodyneQ.map (𝟙 Y.right) at h
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] at h
    have hc : IsIso (AnodyneHomotopy.anodyneQ.map j.right ≫
        AnodyneHomotopy.anodyneQ.map p.right) := by rw [h]; infer_instance
    exact (isIso_comp_right_iff _ _).mp hc
  have hml : Mono (pushout.inl X.hom Y.hom) :=
    (MorphismProperty.monomorphisms SSet.{v}).of_isPushout
      (IsPushout.of_hasPushout X.hom Y.hom) inferInstance
  have hmr : Mono (pushout.inr X.hom Y.hom) :=
    (MorphismProperty.monomorphisms SSet.{v}).of_isPushout
      (IsPushout.of_hasPushout X.hom Y.hom).flip inferInstance
  have : Mono i.right := by change Mono (pushout.inl X.hom Y.hom ≫ left c); infer_instance
  have : Mono j.right := by change Mono (pushout.inr X.hom Y.hom ≫ left c); infer_instance
  have : IsIso (F.map i) := hF i inferInstance hi
  have : IsIso (F.map j) := hF j inferInstance hj
  have hp : IsIso (F.map p) := by
    have h := congrArg F.map hjp
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] at h
    have hc : IsIso (F.map j ≫ F.map p) := by rw [h]; infer_instance
    exact (isIso_comp_left_iff _ _).mp hc
  have h := congrArg F.map hip
  rw [CategoryTheory.Functor.map_comp] at h
  exact h ▸ inferInstanceAs (IsIso (F.map i ≫ F.map p))

end SerrePositivity.SimplicialModel.UnderMonoBrown
