module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.HomotopyClassesClosed

/-! # Actual retraction homotopies give bijections on postcomposition classes

The closed adjunction then detects original map classes from unit-valued
postcomposition tests of the actual internal-Hom restriction map.
-/

@[expose] public section
universe v
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed

namespace SerrePositivity.SimplicialModel.HomotopyRetractionTests
open HomotopyClasses

lemma post_bijective {A B : SSet.{v}} (i : A ⟶ B) (r : B ⟶ A)
    (hi : i ≫ r = 𝟙 A) (H : SSet.Homotopy (𝟙 B) (r ≫ i)) (X : SSet.{v}) :
    Function.Bijective (post i (X := X)) := by
  have hl : Function.LeftInverse (post r (X := X)) (post i) := by
    intro x
    refine Quot.inductionOn x (fun f => ?_)
    change mk ((f ≫ i) ≫ r) = mk f
    rw [Category.assoc, hi, Category.comp_id]
  have hr : Function.RightInverse (post r (X := X)) (post i) := by
    intro x
    refine Quot.inductionOn x (fun f => ?_)
    change mk ((f ≫ r) ≫ i) = mk f
    have h := congrArg (pre f) (sound H)
    simpa only [pre_mk, Category.assoc, Category.comp_id] using h.symm
  exact ⟨hl.injective, hr.surjective⟩

lemma pre_iso_bijective {A B K : SSet.{v}} (e : A ≅ B) :
    Function.Bijective (pre e.hom (K := K)) := by
  have hl : Function.LeftInverse (pre e.inv (K := K)) (pre e.hom) := by
    intro x
    refine Quot.inductionOn x (fun f => ?_)
    change mk (e.inv ≫ (e.hom ≫ f)) = mk f
    rw [← Category.assoc, e.inv_hom_id, Category.id_comp]
  have hr : Function.RightInverse (pre e.inv (K := K)) (pre e.hom) := by
    intro x
    refine Quot.inductionOn x (fun f => ?_)
    change mk (e.hom ≫ (e.inv ≫ f)) = mk f
    rw [← Category.assoc, e.hom_inv_id, Category.id_comp]
  exact ⟨hl.injective, hr.surjective⟩

lemma pre_bijective_of_restriction_post {A B K : SSet.{v}} (i : A ⟶ B)
    (h : Function.Bijective (post ((MonoidalClosed.pre i).app K) (X := 𝟙_ SSet.{v}))) :
    Function.Bijective (pre i (K := K)) := by
  have hρB := pre_iso_bijective (K := K) (ρ_ B)
  have hρA := pre_iso_bijective (K := K) (ρ_ A)
  let eB := HomotopyClassesClosed.equiv (A := B) (X := 𝟙_ SSet.{v}) (K := K)
  let eA := HomotopyClassesClosed.equiv (A := A) (X := 𝟙_ SSet.{v}) (K := K)
  have hs : pre (i ▷ (𝟙_ SSet.{v})) (K := K) =
      eA.symm ∘ post ((MonoidalClosed.pre i).app K) ∘ eB := by
    funext x
    have hnat := HomotopyClassesClosed.uncurryClass_post i (eB x)
    change eA.symm (post ((MonoidalClosed.pre i).app K) (eB x)) =
      pre (i ▷ (𝟙_ SSet.{v})) (eB.symm (eB x)) at hnat
    rw [eB.symm_apply_apply] at hnat
    exact hnat.symm
  have ht : Function.Bijective (pre (i ▷ (𝟙_ SSet.{v})) (K := K)) := by
    rw [hs]
    exact eA.symm.bijective.comp (h.comp eB.bijective)
  have hn : pre (ρ_ A).hom (K := K) ∘ pre i =
      pre (i ▷ (𝟙_ SSet.{v})) ∘ pre (ρ_ B).hom := by
    funext x
    refine Quot.inductionOn x (fun f => ?_)
    change mk ((ρ_ A).hom ≫ (i ≫ f)) = mk ((i ▷ _) ≫ ((ρ_ B).hom ≫ f))
    rw [← Category.assoc, ← rightUnitor_naturality, Category.assoc]
  apply (Function.Bijective.of_comp_iff' hρA _).mp
  rw [hn]
  exact ht.comp hρB

end SerrePositivity.SimplicialModel.HomotopyRetractionTests
