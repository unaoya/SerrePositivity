module

public import Mathlib.CategoryTheory.LiftingProperties.ParametrizedAdjunction
public import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty

/-! # Extending pushout-product tests from generators

Parametrized adjunctions turn generator tests into right lifting properties.
Double orthogonality then extends the tests to both generated left classes,
without small-object or model-category hypotheses.
-/

@[expose] public section
universe u₁ v₁ u₂ v₂ u₃ v₃
noncomputable section
open CategoryTheory.Limits
namespace CategoryTheory.ParametrizedAdjunction
variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃]
  {F : C₁ ⥤ C₂ ⥤ C₃} {G : C₁ᵒᵖ ⥤ C₃ ⥤ C₂}
  [HasPushouts C₃] [HasPullbacks C₂]

/-- Fixing the first arrow, tests on P extend to its generated left class. -/
lemma pushout_generated_second (adj : F ⊣₂ G)
    (P : MorphismProperty C₂) (Q : MorphismProperty C₃)
    {A B : C₁} (i : A ⟶ B)
    (h : ∀ {X Y : C₂} (j : X ⟶ Y), P j →
      ∀ sq : F.PushoutObjObj i j, Q.llp sq.ι)
    {X Y : C₂} (j : X ⟶ Y) (hj : P.rlp.llp j)
    (sq : F.PushoutObjObj i j) : Q.llp sq.ι := by
  intro U V p hp
  let pull := Functor.PullbackObjObj.ofHasPullback G i p
  have hr : P.rlp pull.π := by
    intro X' Y' j' hj'
    let push := Functor.PushoutObjObj.ofHasPushout F i j'
    exact (adj.hasLiftingProperty_iff push pull).1 (h j' hj' push p hp)
  exact (adj.hasLiftingProperty_iff sq pull).2 (hj _ hr)

variable {H : C₂ᵒᵖ ⥤ C₃ ⥤ C₁} [HasPullbacks C₁]

/-- Testing the original generators in both variables suffices for both
generated left classes. The target class must be a left lifting class. -/
lemma pushout_generated_both (adj : F ⊣₂ G) (adjFlip : F.flip ⊣₂ H)
    (P₁ : MorphismProperty C₁) (P₂ : MorphismProperty C₂) (Q : MorphismProperty C₃)
    (h : ∀ {A B : C₁} (i : A ⟶ B), P₁ i →
      ∀ {X Y : C₂} (j : X ⟶ Y), P₂ j →
      ∀ sq : F.PushoutObjObj i j, Q.llp sq.ι)
    {A B : C₁} (i : A ⟶ B) (hi : P₁.rlp.llp i)
    {X Y : C₂} (j : X ⟶ Y) (hj : P₂.rlp.llp j)
    (sq : F.PushoutObjObj i j) : Q.llp sq.ι := by
  apply adjFlip.pushout_generated_second P₁ Q j _ i hi sq.flip
  intro A' B' i' hi' sq'
  exact adj.pushout_generated_second P₂ Q i' (h i' hi') j hj sq'.flip

end CategoryTheory.ParametrizedAdjunction
