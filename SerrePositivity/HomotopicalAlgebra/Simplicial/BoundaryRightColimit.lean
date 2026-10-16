module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.Generators
public import SerrePositivity.HomotopicalAlgebra.Simplicial.MonoRightLiftingContraction
public import SerrePositivity.HomotopicalAlgebra.Smith.AccessibleLiftingClosure
public import Mathlib.CategoryTheory.Category.ULift

/-! # Filtered and sequential colimits of actual boundary-right arrows

Finite presentability of both endpoints of each boundary generator gives
the lifting property on the original colimit. A lifted index category
handles actual natural-number diagrams in any value universe.
-/

@[expose] public section
universe v
noncomputable section
open CategoryTheory CategoryTheory.Limits
open SSet.modelCategoryQuillen
attribute [local instance] Cardinal.fact_isRegular_aleph0

namespace SerrePositivity.SimplicialModel.BoundaryRightColimit

lemma filtered_rlp {J : Type v} [SmallCategory J] [IsFiltered J]
    {F : J ⥤ Arrow SSet.{v}} {c : Cocone F} (hc : IsColimit c)
    (hF : ∀ j, I.rlp (F.obj j).hom) : I.rlp c.pt.hom := by
  have : IsCardinalFiltered J Cardinal.aleph0.{v} :=
    (isCardinalFiltered_aleph0_iff J).mpr inferInstance
  have hdom : ∀ i : I.{v}.toSet, IsCardinalPresentable i.val.left Cardinal.aleph0.{v} := by
    rintro ⟨f, hf⟩
    rcases f with ⟨A, B, f⟩
    cases hf with
    | mk n =>
      change IsCardinalPresentable (SSet.boundary.{v} n).toSSet Cardinal.aleph0.{v}
      infer_instance
  have hcod : ∀ i : I.{v}.toSet, IsCardinalPresentable i.val.right Cardinal.aleph0.{v} := by
    rintro ⟨f, hf⟩
    rcases f with ⟨A, B, f⟩
    cases hf with
    | mk n =>
      change IsCardinalPresentable (SSet.stdSimplex.{v}.obj (SimplexCategory.mk n))
        Cardinal.aleph0.{v}
      infer_instance
  exact @Smith.AccessibleLiftingClosure.rlp_of_isColimit.{v, v, v + 1}
    SSet.{v} _ _ I.{v} Cardinal.aleph0.{v} _ hdom hcod J _ _ F c hc hF

lemma sequential_rlp {F : ℕ ⥤ Arrow SSet.{v}} {c : Cocone F} (hc : IsColimit c)
    (hF : ∀ n, I.rlp (F.obj n).hom) : I.rlp c.pt.hom := by
  let e := (AsSmall.equiv.{0, 0, v} (C := ℕ)).symm
  have : IsFiltered (AsSmall.{v} ℕ) := IsFiltered.of_equivalence (AsSmall.equiv.{0, 0, v} (C := ℕ))
  exact filtered_rlp (J := AsSmall.{v} ℕ) (F := e.functor ⋙ F)
    (c := c.whisker e.functor) (hc.whiskerEquivalence e) (fun n => hF (e.functor.obj n))

lemma sequential_localized_isIso {F : ℕ ⥤ Arrow SSet.{v}} {c : Cocone F} (hc : IsColimit c)
    (hF : ∀ n, I.rlp (F.obj n).hom) :
    IsIso (AnodyneHomotopy.anodyneQ.map c.pt.hom) := by
  have h := sequential_rlp hc hF
  rw [← SSet.rlp_monomorphisms] at h
  exact MonoRightLiftingContraction.localized_isIso _ h

end SerrePositivity.SimplicialModel.BoundaryRightColimit
