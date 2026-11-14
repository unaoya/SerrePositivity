module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.HomotopicalAlgebra.Quillen.Adjunction
public import Mathlib.CategoryTheory.LiftingProperties.ParametrizedAdjunction
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant

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

theorem isQuillenBifunctor_flip_iff (F : C₁ ⥤ C₂ ⥤ C₃) :
    IsQuillenBifunctor F.flip ↔ IsQuillenBifunctor F := by
  constructor
  · intro h
    have := h
    exact isQuillenBifunctor_flip F.flip
  · intro h
    have := h
    infer_instance

/-- Fixing a cofibrant parameter gives a left Quillen functor. Preservation
of initial objects in the other variable is obtained from its ordinary adjoints. -/
lemma isLeftQuillen_obj_of_cofibrant (F : C₁ ⥤ C₂ ⥤ C₃) [IsQuillenBifunctor F]
    [∀ X : C₂, (F.flip.obj X).IsLeftAdjoint] (A : C₁) [IsCofibrant A] :
    IsLeftQuillen (F.obj A) := by
  constructor
  · intro X Y j hj
    have hjC : Cofibration j := (cofibration_iff _).2 hj
    let s := Functor.PushoutObjObj.ofIsInitialLeft F (Limits.initial.to A) j
      Limits.initialIsInitial
    have h := IsQuillenBifunctor.cofibration (Limits.initial.to A) j s inferInstance hjC
    exact (cofibration_iff _).1 h
  · intro X Y j hj
    obtain ⟨hjC, hjW⟩ := (mem_trivialCofibrations_iff j).1 hj
    let s := Functor.PushoutObjObj.ofIsInitialLeft F (Limits.initial.to A) j
      Limits.initialIsInitial
    exact ⟨(cofibration_iff _).1
      (IsQuillenBifunctor.cofibration (Limits.initial.to A) j s inferInstance hjC),
      (weakEquivalence_iff _).1
      (IsQuillenBifunctor.weakEquivalence (Limits.initial.to A) j s
        inferInstance hjC (Or.inr hjW))⟩

end SerrePositivity.Quillen

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "A.3.1.1" (partial := component) "仮定：三つの抽象モデル圏と二変数 functor（HTT と一致）。結論：cofibration 二つの pushout-product が cofibration で、片方が trivial なら trivial という (a) を正確に表す。IsQuillenBifunctor 自体は (b) の各変数での小余極限保存を課さず、その条件は別の adjunction/PreservesColimits として渡す必要がある。"] _root_.SerrePositivity.Quillen.IsQuillenBifunctor
attribute [cite HTT "A.3.1.5"] _root_.SerrePositivity.Quillen.IsQuillenBifunctor
