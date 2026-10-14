module

public import SerrePositivity.HomotopicalAlgebra.Quillen.Adjunction
public import Mathlib.CategoryTheory.LiftingProperties.ParametrizedAdjunction

/-!
# Quillen bifunctors and the pullback-hom criterion

The two-variable adjunction data are existing Mathlib parametrized adjunctions.
The new predicates concern the chosen model structures only. Pushouts and
pullbacks are represented by Mathlib's `PushoutObjObj` and `PullbackObjObj`;
the statements apply to any choices of these squares.
-/

@[expose] public section

universe u₁ v₁ u₂ v₂ u₃ v₃

open CategoryTheory HomotopicalAlgebra

namespace SerrePositivity.Quillen

variable {C₁ : Type u₁} [Category.{v₁} C₁] [ModelCategory C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [ModelCategory C₂]
  {C₃ : Type u₃} [Category.{v₃} C₃] [ModelCategory C₃]

/-- The pushout-product preservation conditions. Ordinary adjoints in both
variables are supplied separately when this predicate is used as a Quillen
two-variable adjunction. -/
class IsQuillenBifunctor (F : C₁ ⥤ C₂ ⥤ C₃) : Prop where
  cofibration {A B : C₁} {X Y : C₂} (i : A ⟶ B) (j : X ⟶ Y)
    (sq : F.PushoutObjObj i j) : Cofibration i → Cofibration j → Cofibration sq.ι
  weakEquivalence {A B : C₁} {X Y : C₂} (i : A ⟶ B) (j : X ⟶ Y)
    (sq : F.PushoutObjObj i j) : Cofibration i → Cofibration j →
      (WeakEquivalence i ∨ WeakEquivalence j) → WeakEquivalence sq.ι

/-- The equivalent right-hand condition on a parametrized right adjoint. -/
class HasQuillenPullbackHom (G : C₁ᵒᵖ ⥤ C₃ ⥤ C₂) : Prop where
  fibration {A B : C₁} {X Y : C₃} (i : A ⟶ B) (p : X ⟶ Y)
    (sq : G.PullbackObjObj i p) : Cofibration i → Fibration p → Fibration sq.π
  weakEquivalence {A B : C₁} {X Y : C₃} (i : A ⟶ B) (p : X ⟶ Y)
    (sq : G.PullbackObjObj i p) : Cofibration i → Fibration p →
      (WeakEquivalence i ∨ WeakEquivalence p) → WeakEquivalence sq.π

theorem isQuillenBifunctor_iff_pullbackHom {F : C₁ ⥤ C₂ ⥤ C₃}
    {G : C₁ᵒᵖ ⥤ C₃ ⥤ C₂} (adj : F ⊣₂ G) :
    IsQuillenBifunctor F ↔ HasQuillenPullbackHom G := by
  constructor
  · intro h
    have hfib {A B : C₁} {X Y : C₃} (i : A ⟶ B) (p : X ⟶ Y)
        (sq : G.PullbackObjObj i p) (hi : Cofibration i) (hp : Fibration p) :
        Fibration sq.π := by
      rw [fibration_iff, ← trivialCofibrations_rlp]
      intro U V j hj
      obtain ⟨hjC, hjW⟩ := (mem_trivialCofibrations_iff j).1 hj
      let s := Functor.PushoutObjObj.ofHasPushout F i j
      have := h.cofibration i j s hi hjC
      have := h.weakEquivalence i j s hi hjC (Or.inr hjW)
      have := hp
      exact (adj.hasLiftingProperty_iff s sq).1 inferInstance
    refine ⟨hfib, ?_⟩
    intro A B X Y i p sq hi hp hw
    have ht : trivialFibrations C₂ sq.π := by
      rw [← cofibrations_rlp]
      intro U V j hj
      have hjC : Cofibration j := (cofibration_iff j).2 hj
      let s := Functor.PushoutObjObj.ofHasPushout F i j
      have := h.cofibration i j s hi hjC
      have := hp
      have hlift : HasLiftingProperty s.ι p := by
        rcases hw with hw | hw
        · have := h.weakEquivalence i j s hi hjC (Or.inl hw)
          infer_instance
        · have := hw
          infer_instance
      exact (adj.hasLiftingProperty_iff s sq).1 hlift
    exact (weakEquivalence_iff _).2 ht.2
  · intro h
    have hcof {A B : C₁} {X Y : C₂} (i : A ⟶ B) (j : X ⟶ Y)
        (sq : F.PushoutObjObj i j) (hi : Cofibration i) (hj : Cofibration j) :
        Cofibration sq.ι := by
      rw [cofibration_iff, ← trivialFibrations_llp]
      intro U V p hp
      obtain ⟨hpF, hpW⟩ := (mem_trivialFibrations_iff p).1 hp
      let s := Functor.PullbackObjObj.ofHasPullback G i p
      have := h.fibration i p s hi hpF
      have := h.weakEquivalence i p s hi hpF (Or.inr hpW)
      have := hj
      exact (adj.hasLiftingProperty_iff sq s).2 inferInstance
    refine ⟨hcof, ?_⟩
    intro A B X Y i j sq hi hj hw
    have ht : trivialCofibrations C₃ sq.ι := by
      rw [← fibrations_llp]
      intro U V p hp
      have hpF : Fibration p := (fibration_iff p).2 hp
      let s := Functor.PullbackObjObj.ofHasPullback G i p
      have := h.fibration i p s hi hpF
      have := hj
      have hlift : HasLiftingProperty j s.π := by
        rcases hw with hw | hw
        · have := h.weakEquivalence i p s hi hpF (Or.inl hw)
          infer_instance
        · have := hw
          infer_instance
      exact (adj.hasLiftingProperty_iff sq s).2 hlift
    exact (weakEquivalence_iff _).2 ht.2

/-- The two pushout-product variables can be exchanged without changing the
preservation conditions; no symmetry of the target category is required. -/
instance isQuillenBifunctor_flip (F : C₁ ⥤ C₂ ⥤ C₃) [IsQuillenBifunctor F] :
    IsQuillenBifunctor F.flip where
  cofibration i j sq hi hj := IsQuillenBifunctor.cofibration (F := F) j i sq.flip hj hi
  weakEquivalence i j sq hi hj hw :=
    IsQuillenBifunctor.weakEquivalence (F := F) j i sq.flip hj hi hw.symm

end SerrePositivity.Quillen
