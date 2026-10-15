module

public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import Mathlib.CategoryTheory.MorphismProperty.Retract
public import Mathlib.CategoryTheory.Functor.Currying

/-! # Locality tests for an actual mapping bifunctor

This purely categorical layer constructs the local-object predicate and the
class detected by all local objects. It does not assume a localized model.
Weak natural transformations of mapping bifunctors preserve both definitions.
-/

@[expose] public section
universe v u vD uD
open CategoryTheory

namespace SerrePositivity.Bousfield.MappingTests
variable {C : Type u} [Category.{v} C] {D : Type uD} [Category.{vD} D]
  (R : Cᵒᵖ ⥤ C ⥤ D) (W : MorphismProperty D)

/-- The maps inverted by mapping into Y. -/
def test (Y : C) : MorphismProperty C :=
  (W.inverseImage (R ⋙ (evaluation C D).obj Y)).unop

@[simp] lemma test_iff (Y : C) {X Z : C} (f : X ⟶ Z) :
    test R W Y f ↔ W ((R.map f.op).app Y) := Iff.rfl

def localObjects (S : MorphismProperty C) (Y : C) : Prop := S ≤ test R W Y

/-- All mapping tests against local objects, without a smallness assertion. -/
def localEquivalences (S : MorphismProperty C) : MorphismProperty C :=
  fun _ _ f => ∀ Y, localObjects R W S Y → test R W Y f

lemma generators_le (S : MorphismProperty C) : S ≤ localEquivalences R W S :=
  fun _ _ f hf _Y hY => hY f hf

lemma localObjects_antitone {S T : MorphismProperty C} (h : S ≤ T) {Y : C}
    (hY : localObjects R W T Y) : localObjects R W S Y := h.trans hY

lemma localEquivalences_monotone {S T : MorphismProperty C} (h : S ≤ T) :
    localEquivalences R W S ≤ localEquivalences R W T :=
  fun _ _ _f hf Y hY => hf Y (localObjects_antitone R W h hY)

@[simp] lemma localObjects_bot (Y : C) : localObjects R W ⊥ Y := bot_le

lemma localObjects_sup (S T : MorphismProperty C) (Y : C) :
    localObjects R W (S ⊔ T) Y ↔ localObjects R W S Y ∧ localObjects R W T Y :=
  sup_le_iff

lemma localEquivalences_eq_of_localObjects {S T : MorphismProperty C}
    (h : localObjects R W S = localObjects R W T) :
    localEquivalences R W S = localEquivalences R W T := by
  ext X Z f
  simp only [localEquivalences, h]

/-- Closing the test maps under all local tests does not change the local objects. -/
lemma localObjects_closure (S : MorphismProperty C) :
    localObjects R W (localEquivalences R W S) = localObjects R W S := by
  funext Y
  apply propext
  constructor
  · exact fun h => (generators_le R W S).trans h
  · exact fun h _ _ f hf => hf Y h

lemma localEquivalences_idempotent (S : MorphismProperty C) :
    localEquivalences R W (localEquivalences R W S) = localEquivalences R W S :=
  localEquivalences_eq_of_localObjects R W (localObjects_closure R W S)

instance test_containsIdentities [W.ContainsIdentities] (Y : C) :
    (test R W Y).ContainsIdentities := by unfold test; infer_instance

instance test_twoOutOfThree [W.HasTwoOutOfThreeProperty] (Y : C) :
    (test R W Y).HasTwoOutOfThreeProperty := by unfold test; infer_instance

instance test_retracts [W.IsStableUnderRetracts] (Y : C) :
    (test R W Y).IsStableUnderRetracts := by unfold test; infer_instance

instance localEquivalences_containsIdentities [W.ContainsIdentities] (S : MorphismProperty C) :
    (localEquivalences R W S).ContainsIdentities where
  id_mem X Y _ := (test R W Y).id_mem X

instance localEquivalences_twoOutOfThree [W.HasTwoOutOfThreeProperty]
    (S : MorphismProperty C) : (localEquivalences R W S).HasTwoOutOfThreeProperty where
  comp_mem f g hf hg Y hY := (test R W Y).comp_mem f g (hf Y hY) (hg Y hY)
  of_precomp f g hf hfg Y hY := (test R W Y).of_precomp f g (hf Y hY) (hfg Y hY)
  of_postcomp f g hg hfg Y hY := (test R W Y).of_postcomp f g (hg Y hY) (hfg Y hY)

instance localEquivalences_retracts [W.IsStableUnderRetracts] (S : MorphismProperty C) :
    (localEquivalences R W S).IsStableUnderRetracts where
  of_retract h hg Y hY := (test R W Y).of_retract h (hg Y hY)

/-- A weak natural comparison transports a mapping test by two-out-of-three. -/
lemma test_eq_of_weakComparison [W.HasTwoOutOfThreeProperty]
    {R' : Cᵒᵖ ⥤ C ⥤ D} (a : R ⟶ R')
    (ha : ∀ X Y, W ((a.app X).app Y)) (Y : C) : test R W Y = test R' W Y := by
  ext X Z f
  have h := congr_app (a.naturality f.op) Y
  change (R.map f.op).app Y ≫ (a.app (Opposite.op X)).app Y =
    (a.app (Opposite.op Z)).app Y ≫ (R'.map f.op).app Y at h
  change W ((R.map f.op).app Y) ↔ W ((R'.map f.op).app Y)
  constructor
  · intro hf
    exact W.of_precomp _ _ (ha _ Y)
      (h ▸ W.comp_mem _ _ hf (ha _ Y))
  · intro hf
    exact W.of_postcomp _ _ (ha _ Y)
      (h.symm ▸ W.comp_mem _ _ (ha _ Y) hf)

lemma localObjects_eq_of_tests {R' : Cᵒᵖ ⥤ C ⥤ D}
    (h : ∀ Y, test R W Y = test R' W Y) (S : MorphismProperty C) :
    localObjects R W S = localObjects R' W S := by
  funext Y
  unfold localObjects
  rw [h Y]

/-- Objectwise weak equivalences in the target variable preserve every test. -/
lemma test_eq_of_target [W.HasTwoOutOfThreeProperty] {Y Z : C} (q : Y ⟶ Z)
    (hq : ∀ X, W ((R.obj X).map q)) : test R W Y = test R W Z := by
  ext X X' f
  have h := (R.map f.op).naturality q
  change W ((R.map f.op).app Y) ↔ W ((R.map f.op).app Z)
  constructor
  · intro hf
    exact W.of_precomp _ _ (hq _) (h ▸ W.comp_mem _ _ hf (hq _))
  · intro hf
    exact W.of_postcomp _ _ (hq _) (h.symm ▸ W.comp_mem _ _ (hq _) hf)

/-- A weak square between representatives gives the same locality test. -/
lemma test_arrow_iff [W.HasTwoOutOfThreeProperty] (Y : C)
    {X Z X' Z' : C} {f : X ⟶ Z} {g : X' ⟶ Z'}
    (a : Arrow.mk f ⟶ Arrow.mk g)
    (hl : test R W Y a.left) (hr : test R W Y a.right) :
    test R W Y f ↔ test R W Y g := by
  constructor
  · intro hf
    exact (test R W Y).of_precomp _ _ hl
      (a.w ▸ (test R W Y).comp_mem _ _ hf hr)
  · intro hg
    exact (test R W Y).of_postcomp _ _ hr
      (a.w.symm ▸ (test R W Y).comp_mem _ _ hl hg)

lemma localEquivalences_eq_of_tests {R' : Cᵒᵖ ⥤ C ⥤ D}
    (h : ∀ Y, test R W Y = test R' W Y) (S : MorphismProperty C) :
    localEquivalences R W S = localEquivalences R' W S := by
  have ho := localObjects_eq_of_tests R W h S
  ext X Z f
  simp only [localEquivalences, ho, h]

end SerrePositivity.Bousfield.MappingTests
