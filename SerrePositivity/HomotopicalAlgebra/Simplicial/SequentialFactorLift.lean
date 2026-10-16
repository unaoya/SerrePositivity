module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.SequentialFactorLiftingClasses
public import Mathlib.CategoryTheory.LiftingProperties.Adjunction

/-! # Coherent lifts of the actual sequential left factor

At every successor, the chosen lift extends the previous actual lift by
using its relative pushout. The final natural transformation therefore
solves the original square against a constant arrow.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.SimplicialModel.SequentialFactorLift
open SequentialBoundaryFactorization MonoLocalizedFactorization
variable {F G : ℕ ⥤ SSet.{v}} (α : F ⟶ G) {X Y : SSet.{v}} (p : X ⟶ Y)
  (a : F ⟶ (Functor.const ℕ).obj X) (b : diagram α ⟶ (Functor.const ℕ).obj Y)
  (sq : CommSq a (leftMap α) ((Functor.const ℕ).map p) b)

structure Partial (n : ℕ) where
  hom : (stage α n).obj ⟶ X
  left_fac : (stage α n).i ≫ hom = a.app n
  right_fac : hom ≫ p = b.app n

variable (h₀ : HasLiftingProperty (stage α 0).i p)
  (hs : ∀ n, HasLiftingProperty (left (successorArrow α n (stage α n))) p)

include sq h₀ in
def initial : Partial α p a b 0 := by
  letI := h₀
  let s : CommSq (a.app 0) (stage α 0).i p (b.app 0) := ⟨congr_app sq.w 0⟩
  exact ⟨s.lift, s.fac_left, s.fac_right⟩

def boundaryMap (n : ℕ) (x : Partial α p a b n) :
    pushout (stepMap F n) (stage α n).i ⟶ X :=
  pushout.desc (a.app (n + 1)) x.hom (by
    rw [x.left_fac]
    have h := a.naturality (homOfLE (Nat.le_succ n))
    change stepMap F n ≫ a.app (n + 1) = a.app n ≫ 𝟙 X at h
    exact h.trans (Category.comp_id _))

include sq in
lemma successor_square (n : ℕ) (x : Partial α p a b n) :
    CommSq (boundaryMap α p a b n x) (left (successorArrow α n (stage α n)))
      p (b.app (n + 1)) := by
  constructor
  apply (IsPushout.of_hasPushout (stepMap F n) (stage α n).i).hom_ext
  · dsimp only [boundaryMap]
    rw [← Category.assoc, pushout.inl_desc]
    exact congr_app sq.w (n + 1)
  · dsimp only [boundaryMap]
    rw [← Category.assoc, pushout.inr_desc, x.right_fac]
    change b.app n = transition α n ≫ b.app (n + 1)
    have h := b.naturality (homOfLE (Nat.le_succ n))
    change (diagram α).map (homOfLE (Nat.le_succ n)) ≫ b.app (n + 1) =
      b.app n ≫ 𝟙 Y at h
    have h' := h.trans (Category.comp_id _)
    dsimp only [diagram] at h'
    rw [CategoryTheory.Functor.ofSequence_map_homOfLE_succ] at h'
    exact h'.symm

include sq hs in
def successor (n : ℕ) (x : Partial α p a b n) : Partial α p a b (n + 1) := by
  letI := hs n
  let s := successor_square α p a b sq n x
  refine ⟨s.lift, ?_, s.fac_right⟩
  change (pushout.inl _ _ ≫ left (successorArrow α n (stage α n))) ≫ s.lift = _
  rw [Category.assoc, s.fac_left]
  exact pushout.inl_desc _ _ _

include hs in
lemma successor_previous (n : ℕ) (x : Partial α p a b n) :
    transition α n ≫ (successor α p a b sq hs n x).hom = x.hom := by
  change (pushout.inr _ _ ≫ left (successorArrow α n (stage α n))) ≫
    (successor_square α p a b sq n x).lift = _
  rw [Category.assoc, CommSq.fac_left]
  exact pushout.inr_desc _ _ _

include sq h₀ hs in
def stageLift : ∀ n, Partial α p a b n
  | 0 => initial α p a b sq h₀
  | n + 1 => successor α p a b sq hs n (stageLift n)

include sq h₀ hs in
def lift : diagram α ⟶ (Functor.const ℕ).obj X :=
  NatTrans.ofSequence (fun n => (stageLift α p a b sq h₀ hs n).hom) (by
    intro n
    change (diagram α).map (homOfLE (Nat.le_succ n)) ≫
      (stageLift α p a b sq h₀ hs (n + 1)).hom =
      (stageLift α p a b sq h₀ hs n).hom ≫ 𝟙 X
    dsimp only [diagram]
    rw [CategoryTheory.Functor.ofSequence_map_homOfLE_succ, Category.comp_id]
    exact successor_previous α p a b sq hs n _)

include h₀ hs in
lemma lift_left : leftMap α ≫ lift α p a b sq h₀ hs = a := by
  apply NatTrans.ext
  funext n
  exact (stageLift α p a b sq h₀ hs n).left_fac

include h₀ hs in
lemma lift_right : lift α p a b sq h₀ hs ≫ (Functor.const ℕ).map p = b := by
  apply NatTrans.ext
  funext n
  exact (stageLift α p a b sq h₀ hs n).right_fac

include h₀ hs in
lemma hasLiftingProperty : HasLiftingProperty (leftMap α) ((Functor.const ℕ).map p) := by
  constructor
  intro a b sq
  exact CommSq.HasLift.mk'
    { l := lift α p a b sq h₀ hs
      fac_left := lift_left α p a b sq h₀ hs
      fac_right := lift_right α p a b sq h₀ hs }

end SerrePositivity.SimplicialModel.SequentialFactorLift
