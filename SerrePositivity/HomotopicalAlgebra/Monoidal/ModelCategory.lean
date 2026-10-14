module

public import SerrePositivity.HomotopicalAlgebra.Monoidal.QuillenBifunctor
public import Mathlib.CategoryTheory.LiftingProperties.PushoutProduct
public import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant

/-!
# Monoidal model compatibility and the separate unit axiom

These are properties of the existing monoidal category and model structure.
The unit need not be cofibrant: the unit axiom specifies a cofibrant replacement
and requires its left and right tensor maps on cofibrant objects to be weak
equivalences. It is not inferred from the pushout-product condition.
-/

@[expose] public section

universe u v

open CategoryTheory HomotopicalAlgebra CategoryTheory.MonoidalCategory

namespace SerrePositivity.Quillen

variable (C : Type u) [Category.{v} C] [ModelCategory C] [MonoidalCategory C]

/-- The unit axiom for a specified replacement of the monoidal unit. -/
structure UnitReplacementAxiom (Q : C) (q : Q ⟶ 𝟙_ C) : Prop where
  cofibrant : IsCofibrant Q
  weakEquivalence : WeakEquivalence q
  left (X : C) : IsCofibrant X → WeakEquivalence (q ▷ X)
  right (X : C) : IsCofibrant X → WeakEquivalence (X ◁ q)

/-- Existence of a replacement satisfying the unit axiom, independently of
the pushout-product condition. -/
class HasUnitAxiom : Prop where
  exists_replacement : ∃ (Q : C) (q : Q ⟶ 𝟙_ C), UnitReplacementAxiom C Q q

/-- A monoidal model category is the existing model and monoidal structures
with pushout-product compatibility and the separate unit axiom. -/
class MonoidalModelCategory : Prop where
  pushoutProduct : IsQuillenBifunctor (curriedTensor C)
  unit : HasUnitAxiom C

attribute [instance] MonoidalModelCategory.pushoutProduct MonoidalModelCategory.unit

/-- A cofibrant unit satisfies the unit axiom using its identity replacement. -/
lemma unitAxiom_of_cofibrant_unit [IsCofibrant (𝟙_ C)] : HasUnitAxiom C := by
  refine ⟨𝟙_ C, 𝟙 _, ?_⟩
  refine ⟨inferInstance, inferInstance, ?_, ?_⟩
  · intro X _
    simp only [MonoidalCategory.id_whiskerRight]
    infer_instance
  · intro X _
    simp only [MonoidalCategory.whiskerLeft_id]
    infer_instance

variable [MonoidalClosed C]

/-- The closed monoidal pushout-product condition is exactly the
pullback-hom fibration condition; the unit axiom remains a separate conjunct. -/
theorem monoidalModelCategory_iff : MonoidalModelCategory C ↔
    HasQuillenPullbackHom (MonoidalClosed.internalHom (C := C)) ∧ HasUnitAxiom C := by
  constructor
  · intro h
    exact ⟨(isQuillenBifunctor_iff_pullbackHom (MonoidalClosed.internalHomAdjunction₂ (C := C))).1
      h.pushoutProduct, h.unit⟩
  · rintro ⟨h, hu⟩
    exact ⟨(isQuillenBifunctor_iff_pullbackHom
      (MonoidalClosed.internalHomAdjunction₂ (C := C))).2 h,
      hu⟩

omit [MonoidalClosed C] in
/-- Canonical Mathlib pushout-products satisfy the cofibration condition. -/
lemma pushoutProduct_cofibration [IsQuillenBifunctor (curriedTensor C)]
    {A B X Y : C} (i : A ⟶ B) (j : X ⟶ Y) [Cofibration i] [Cofibration j] :
    Cofibration (Arrow.mk i □ Arrow.mk j).hom :=
  IsQuillenBifunctor.cofibration i j (Functor.PushoutObjObj.ofHasPushout _ i j)
    inferInstance inferInstance

omit [MonoidalClosed C] in
lemma pushoutProduct_weakEquivalence [IsQuillenBifunctor (curriedTensor C)]
    {A B X Y : C} (i : A ⟶ B) (j : X ⟶ Y) [Cofibration i] [Cofibration j]
    (h : WeakEquivalence i ∨ WeakEquivalence j) : WeakEquivalence (Arrow.mk i □ Arrow.mk j).hom :=
  IsQuillenBifunctor.weakEquivalence i j (Functor.PushoutObjObj.ofHasPushout _ i j)
    inferInstance inferInstance h

/-- The canonical closed pullback-hom is a fibration, and is trivial when
either input is trivial. -/
lemma pullbackHom_fibration [HasQuillenPullbackHom (MonoidalClosed.internalHom (C := C))]
    {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y) [Cofibration i] [Fibration p] :
    Fibration ((.op (Arrow.mk i)) ⋔ Arrow.mk p).hom :=
  HasQuillenPullbackHom.fibration i p (Functor.PullbackObjObj.ofHasPullback _ i p)
    inferInstance inferInstance

lemma pullbackHom_weakEquivalence [HasQuillenPullbackHom (MonoidalClosed.internalHom (C := C))]
    {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y) [Cofibration i] [Fibration p]
    (h : WeakEquivalence i ∨ WeakEquivalence p) :
    WeakEquivalence ((.op (Arrow.mk i)) ⋔ Arrow.mk p).hom :=
  HasQuillenPullbackHom.weakEquivalence i p (Functor.PullbackObjObj.ofHasPullback _ i p)
    inferInstance inferInstance h

end SerrePositivity.Quillen
