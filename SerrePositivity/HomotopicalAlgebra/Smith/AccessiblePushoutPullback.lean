module

public import SerrePositivity.HomotopicalAlgebra.Smith.AccessibleLimits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-! # Accessibility of pushouts and pullbacks of functors

Canonical evaluation isomorphisms compare these functors with the actual
pointwise pushout/pullback objects. No definitional equality of independently
chosen colimits or limits is required.
-/

@[expose] public section
universe w v u v' u'
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.Smith.AccessiblePushoutPullback
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

lemma pushout_isAccessible [HasPushouts C] {A B E : D ⥤ C} (α : A ⟶ B) (β : A ⟶ E)
    [A.IsAccessible.{w}] [B.IsAccessible.{w}] [E.IsAccessible.{w}] :
    (pushout α β).IsAccessible.{w} := by
  have : ∀ k, ((span α β).obj k).IsAccessible.{w} := by
    rintro (_ | (_ | _))
    · exact inferInstanceAs (A.IsAccessible.{w})
    · exact inferInstanceAs (B.IsAccessible.{w})
    · exact inferInstanceAs (E.IsAccessible.{w})
  obtain ⟨κ, hκ, h⟩ := exists_common_accessibility.{w} (fun k ↦ (span α β).obj k)
  have := AccessibleColimits.colimit_isCardinalAccessible (span α β) κ
  exact Functor.isAccessible_of_isCardinalAccessible (pushout α β) κ

def pushoutEvaluationIso [HasPushouts C] {A B E : D ⥤ C} (α : A ⟶ B) (β : A ⟶ E) (X : D) :
    pushout (α.app X) (β.app X) ≅ (pushout α β).obj X :=
  PreservesPushout.iso ((evaluation D C).obj X) α β

lemma pullback_isAccessible [HasPullbacks C] [IsLocallyPresentable.{w} C]
    {A B E : D ⥤ C} (α : A ⟶ E) (β : B ⟶ E)
    [A.IsAccessible.{w}] [B.IsAccessible.{w}] [E.IsAccessible.{w}] :
    (pullback α β).IsAccessible.{w} := by
  have : ∀ k, ((cospan α β).obj k).IsAccessible.{w} := by
    rintro (_ | (_ | _))
    · exact inferInstanceAs (E.IsAccessible.{w})
    · exact inferInstanceAs (A.IsAccessible.{w})
    · exact inferInstanceAs (B.IsAccessible.{w})
  have := AccessibleLimits.pointwiseLimit_isAccessible.{w} WalkingCospan (cospan α β)
  obtain ⟨κ, hκ, h⟩ := Functor.IsAccessible.exists_cardinal ((cospan α β).flip ⋙ lim)
  have := Functor.isCardinalAccessible_of_natIso (limitIsoFlipCompLim (cospan α β)).symm κ
  exact Functor.isAccessible_of_isCardinalAccessible (pullback α β) κ

def pullbackEvaluationIso [HasPullbacks C] {A B E : D ⥤ C} (α : A ⟶ E) (β : B ⟶ E) (X : D) :
    (pullback α β).obj X ≅ pullback (α.app X) (β.app X) :=
  PreservesPullback.iso ((evaluation D C).obj X) α β

def pointwisePushout [HasPushouts C] {A B E : D ⥤ C} (α : A ⟶ B) (β : A ⟶ E) : D ⥤ C where
  obj X := pushout (α.app X) (β.app X)
  map f := pushout.map _ _ _ _ (B.map f) (E.map f) (A.map f)
    (α.naturality f).symm (β.naturality f).symm
  map_id X := by apply pushout.hom_ext <;> simp
  map_comp f g := by apply pushout.hom_ext <;> simp [Category.assoc]

def pointwisePushoutIso [HasPushouts C] {A B E : D ⥤ C} (α : A ⟶ B) (β : A ⟶ E) :
    pointwisePushout α β ≅ pushout α β :=
  NatIso.ofComponents (pushoutEvaluationIso α β) (by
    intro X Y f
    apply pushout.hom_ext
    · simp only [pointwisePushout, pushout.map, pushout.inl_desc_assoc, Category.assoc]
      have hX : pushout.inl (α.app X) (β.app X) ≫ (pushoutEvaluationIso α β X).hom =
          (pushout.inl α β).app X :=
        PreservesPushout.inl_iso_hom ((evaluation D C).obj X) α β
      have hY : pushout.inl (α.app Y) (β.app Y) ≫ (pushoutEvaluationIso α β Y).hom =
          (pushout.inl α β).app Y :=
        PreservesPushout.inl_iso_hom ((evaluation D C).obj Y) α β
      exact (congrArg (fun k ↦ B.map f ≫ k) hY).trans
        (((pushout.inl α β).naturality f).trans
          ((congrArg (fun k ↦ k ≫ (pushout α β).map f) hX.symm).trans (Category.assoc _ _ _)))
    · simp only [pointwisePushout, pushout.map, pushout.inr_desc_assoc, Category.assoc]
      have hX : pushout.inr (α.app X) (β.app X) ≫ (pushoutEvaluationIso α β X).hom =
          (pushout.inr α β).app X :=
        PreservesPushout.inr_iso_hom ((evaluation D C).obj X) α β
      have hY : pushout.inr (α.app Y) (β.app Y) ≫ (pushoutEvaluationIso α β Y).hom =
          (pushout.inr α β).app Y :=
        PreservesPushout.inr_iso_hom ((evaluation D C).obj Y) α β
      exact (congrArg (fun k ↦ E.map f ≫ k) hY).trans
        (((pushout.inr α β).naturality f).trans
          ((congrArg (fun k ↦ k ≫ (pushout α β).map f) hX.symm).trans (Category.assoc _ _ _))))

lemma pointwisePushout_isAccessible [HasPushouts C] {A B E : D ⥤ C} (α : A ⟶ B) (β : A ⟶ E)
    [A.IsAccessible.{w}] [B.IsAccessible.{w}] [E.IsAccessible.{w}] :
    (pointwisePushout α β).IsAccessible.{w} := by
  have := pushout_isAccessible.{w} α β
  obtain ⟨κ, hκ, h⟩ := Functor.IsAccessible.exists_cardinal (pushout α β)
  have := Functor.isCardinalAccessible_of_natIso (pointwisePushoutIso α β).symm κ
  exact Functor.isAccessible_of_isCardinalAccessible _ κ

def pointwisePullback [HasPullbacks C] {A B E : D ⥤ C} (α : A ⟶ E) (β : B ⟶ E) : D ⥤ C where
  obj X := pullback (α.app X) (β.app X)
  map f := pullback.map _ _ _ _ (A.map f) (B.map f) (E.map f)
    (α.naturality f).symm (β.naturality f).symm
  map_id X := by apply pullback.hom_ext <;> simp
  map_comp f g := by apply pullback.hom_ext <;> simp [Category.assoc]

def pointwisePullbackIso [HasPullbacks C] {A B E : D ⥤ C} (α : A ⟶ E) (β : B ⟶ E) :
    pullback α β ≅ pointwisePullback α β :=
  NatIso.ofComponents (pullbackEvaluationIso α β) (by
    intro X Y f
    apply pullback.hom_ext
    · simp only [Category.assoc, pointwisePullback, pullback.map, pullback.lift_fst]
      have hX : (pullbackEvaluationIso α β X).hom ≫ pullback.fst (α.app X) (β.app X) =
          (pullback.fst α β).app X :=
        PreservesPullback.iso_hom_fst ((evaluation D C).obj X) α β
      have hY : (pullbackEvaluationIso α β Y).hom ≫ pullback.fst (α.app Y) (β.app Y) =
          (pullback.fst α β).app Y :=
        PreservesPullback.iso_hom_fst ((evaluation D C).obj Y) α β
      exact (congrArg (fun k ↦ (pullback α β).map f ≫ k) hY).trans
        (((pullback.fst α β).naturality f).trans
          ((congrArg (fun k ↦ k ≫ A.map f) hX.symm).trans (Category.assoc _ _ _)))
    · simp only [Category.assoc, pointwisePullback, pullback.map, pullback.lift_snd]
      have hX : (pullbackEvaluationIso α β X).hom ≫ pullback.snd (α.app X) (β.app X) =
          (pullback.snd α β).app X :=
        PreservesPullback.iso_hom_snd ((evaluation D C).obj X) α β
      have hY : (pullbackEvaluationIso α β Y).hom ≫ pullback.snd (α.app Y) (β.app Y) =
          (pullback.snd α β).app Y :=
        PreservesPullback.iso_hom_snd ((evaluation D C).obj Y) α β
      exact (congrArg (fun k ↦ (pullback α β).map f ≫ k) hY).trans
        (((pullback.snd α β).naturality f).trans
          ((congrArg (fun k ↦ k ≫ B.map f) hX.symm).trans (Category.assoc _ _ _))))

lemma pointwisePullback_isAccessible [HasPullbacks C] [IsLocallyPresentable.{w} C]
    {A B E : D ⥤ C} (α : A ⟶ E) (β : B ⟶ E)
    [A.IsAccessible.{w}] [B.IsAccessible.{w}] [E.IsAccessible.{w}] :
    (pointwisePullback α β).IsAccessible.{w} := by
  have := pullback_isAccessible.{w} α β
  obtain ⟨κ, hκ, h⟩ := Functor.IsAccessible.exists_cardinal (pullback α β)
  have := Functor.isCardinalAccessible_of_natIso (pointwisePullbackIso α β) κ
  exact Functor.isAccessible_of_isCardinalAccessible _ κ

end SerrePositivity.Smith.AccessiblePushoutPullback
