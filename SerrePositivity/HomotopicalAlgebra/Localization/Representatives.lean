module

public import SerrePositivity.HomotopicalAlgebra.Localization.Basic

/-! # Independence of weakly equivalent arrow representatives

Representatives may be connected by any finite zigzag of squares whose
two vertical maps are original weak equivalences. The sets of maps need
not be the strict images of a single functorial replacement.
-/

@[expose] public section
universe v u
noncomputable section
open CategoryTheory HomotopicalAlgebra

namespace SerrePositivity.Bousfield
variable {C : Type u} [Category.{v} C] [ModelCategory C]

def weakArrowStep (a b : Arrow C) : Prop :=
  ∃ h : a ⟶ b, weakEquivalences C h.left ∧ weakEquivalences C h.right

def SameWeakRepresentatives (S T : MorphismProperty C) : Prop :=
  (∀ a : Arrow C, S a.hom →
    ∃ b : Arrow C, T b.hom ∧ Relation.EqvGen weakArrowStep a b) ∧
  (∀ b : Arrow C, T b.hom →
    ∃ a : Arrow C, S a.hom ∧ Relation.EqvGen weakArrowStep b a)

variable [ModelCategory SSet.{v}]
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)

include hcof in
lemma mappingTest_iff_of_weakArrowZigzag (Y : C) {a b : Arrow C}
    (h : Relation.EqvGen weakArrowStep a b) :
    mappingTest cof fib Y a.hom ↔ mappingTest cof fib Y b.hom := by
  induction h with
  | rel a b h =>
    obtain ⟨f, hl, hr⟩ := h
    exact mappingTest_arrow_iff cof fib hcof Y f hl hr
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

include hcof in
lemma localObjects_eq_of_weakRepresentatives {S T : MorphismProperty C}
    (h : SameWeakRepresentatives S T) : localObjects cof fib S = localObjects cof fib T := by
  funext Y
  apply propext
  constructor
  · intro hY X Z f hf
    obtain ⟨a, ha, hz⟩ := h.2 (Arrow.mk f) hf
    exact (mappingTest_iff_of_weakArrowZigzag cof fib hcof Y hz).mpr (hY a.hom ha)
  · intro hY X Z f hf
    obtain ⟨b, hb, hz⟩ := h.1 (Arrow.mk f) hf
    exact (mappingTest_iff_of_weakArrowZigzag cof fib hcof Y hz).mpr (hY b.hom hb)

include hcof in
lemma localEquivalences_eq_of_weakRepresentatives {S T : MorphismProperty C}
    (h : SameWeakRepresentatives S T) :
    localEquivalences cof fib S = localEquivalences cof fib T :=
  MappingTests.localEquivalences_eq_of_localObjects _ _
    (localObjects_eq_of_weakRepresentatives cof fib hcof h)

end SerrePositivity.Bousfield
