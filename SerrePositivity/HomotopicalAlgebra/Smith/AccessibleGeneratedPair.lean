module

public import SerrePositivity.HomotopicalAlgebra.Smith.AccessibleHomTransport
public import Mathlib.CategoryTheory.Presentable.Adjunction

/-! # Two generated factorizations at one regular cardinal

There is no equality constraint on the hom, object and small-object universes.
-/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.Smith

lemma exists_common_accessible_generated_factorizations
    {C : Type u} [Category.{v} C] [IsLocallyPresentable.{w} C]
    (I J : MorphismProperty C) [I.IsSmall.{w}] [J.IsSmall.{w}] :
    ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular),
      ∃ (dI : MorphismProperty.FunctorialFactorizationData I.rlp.llp I.rlp)
        (dJ : MorphismProperty.FunctorialFactorizationData J.rlp.llp J.rlp),
        dI.Z.IsCardinalAccessible κ ∧ dJ.Z.IsCardinalAccessible κ := by
  let e := ShrinkHoms.equivalence.{w} C
  have : IsLocallyPresentable.{w} (ShrinkHoms C) := e.isLocallyPresentable
  have := locallyPresentable_hasColimits (C := ShrinkHoms C)
  let I' := AccessibleHomTransport.generators I
  let J' := AccessibleHomTransport.generators J
  have : I'.IsSmall.{w} := inferInstance
  have : J'.IsSmall.{w} := inferInstance
  have := hasSmallObjectArgument I'
  have := hasSmallObjectArgument J'
  let a : I'.toSet ⊕ J'.toSet → Arrow (ShrinkHoms C) :=
    Sum.elim (fun i ↦ i.val) (fun j ↦ j.val)
  obtain ⟨κ, hκ, ha⟩ := exists_common_arrow_presentability a
  have : ∀ i : I'.toSet, IsCardinalPresentable i.val.left κ := fun i ↦ (ha (.inl i)).1
  have : ∀ i : I'.toSet, IsCardinalPresentable i.val.right κ := fun i ↦ (ha (.inl i)).2
  have : ∀ j : J'.toSet, IsCardinalPresentable j.val.left κ := fun j ↦ (ha (.inr j)).1
  have : ∀ j : J'.toSet, IsCardinalPresentable j.val.right κ := fun j ↦ (ha (.inr j)).2
  obtain ⟨dI, hdI, _, _⟩ := AccessibleSmallObject.exists_factorization_at I' κ
  obtain ⟨dJ, hdJ, _, _⟩ := AccessibleSmallObject.exists_factorization_at J' κ
  exact ⟨κ, hκ, AccessibleHomTransport.factorization I dI,
    AccessibleHomTransport.factorization J dJ,
    AccessibleHomTransport.factorization_isCardinalAccessible I dI κ,
    AccessibleHomTransport.factorization_isCardinalAccessible J dJ κ⟩

end SerrePositivity.Smith
