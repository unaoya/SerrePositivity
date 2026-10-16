module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.SequentialBoundaryFactorization
public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanLocalizedLeftProper
public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanTestLiftingClass

/-! # Relative successor factors of a sequential localized equivalence

Only the source successor maps are assumed mono. The actual relative
factor constructed at each successor lies in the fixed Kan-test left
lifting class, not merely in an objectwise weak class.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.SimplicialModel.SequentialFactorLiftingClasses
open SequentialBoundaryFactorization MonoLocalizedFactorization KanTestLiftingClass
variable {F G : ℕ ⥤ SSet.{v}} (α : F ⟶ G)

instance left_mono (n : ℕ) : Mono (stage α n).i := by
  induction n with
  | zero => change Mono (left (α.app 0)); infer_instance
  | succ n ih =>
    have : Mono (stage α n).i := ih
    have : Mono (pushout.inl (stepMap F n) (stage α n).i) :=
      (MorphismProperty.monomorphisms SSet.{v}).pushout_inl _ _ inferInstance
    change Mono (pushout.inl _ _ ≫ left (successorArrow α n (stage α n)))
    infer_instance

lemma right_localized_isIso (n : ℕ) :
    IsIso (AnodyneHomotopy.anodyneQ.map (stage α n).p) := by
  have h := (stage α n).hp
  rw [← SSet.rlp_monomorphisms] at h
  exact MonoRightLiftingContraction.localized_isIso _ h

lemma left_localized_isIso (n : ℕ) (hα : IsIso (AnodyneHomotopy.anodyneQ.map (α.app n))) :
    IsIso (AnodyneHomotopy.anodyneQ.map (stage α n).i) := by
  have : IsIso (AnodyneHomotopy.anodyneQ.map (stage α n).p) := right_localized_isIso α n
  have h := congrArg AnodyneHomotopy.anodyneQ.map (stage α n).fac
  rw [CategoryTheory.Functor.map_comp] at h
  exact (isIso_comp_right_iff _ _).mp (h.symm ▸ hα)

lemma initial_llp (hα : IsIso (AnodyneHomotopy.anodyneQ.map (α.app 0))) :
    rightTests.llp (stage α 0).i :=
  localizedMono_le_llp _ ⟨inferInstance, left_localized_isIso α 0 hα⟩

lemma relative_llp (n : ℕ) [Mono (stepMap F n)]
    (hα : ∀ n, IsIso (AnodyneHomotopy.anodyneQ.map (α.app n))) :
    rightTests.llp (left (successorArrow α n (stage α n))) := by
  let t := pushout.inl (stepMap F n) (stage α n).i
  have ht : IsIso (AnodyneHomotopy.anodyneQ.map t) :=
    KanLocalizedLeftProper.localized_isIso (stage α n).i (left_localized_isIso α n (hα n))
      (stepMap F n) (pushout.inr _ _) t (IsPushout.of_hasPushout _ _).flip
  have he : t ≫ left (successorArrow α n (stage α n)) = (stage α (n + 1)).i := rfl
  have h := congrArg AnodyneHomotopy.anodyneQ.map he
  rw [CategoryTheory.Functor.map_comp] at h
  have : IsIso (AnodyneHomotopy.anodyneQ.map t) := ht
  have hw : IsIso (AnodyneHomotopy.anodyneQ.map (left (successorArrow α n (stage α n)))) :=
    (isIso_comp_left_iff _ _).mp (h.symm ▸ left_localized_isIso α (n + 1) (hα (n + 1)))
  exact localizedMono_le_llp _ ⟨inferInstance, hw⟩

end SerrePositivity.SimplicialModel.SequentialFactorLiftingClasses
