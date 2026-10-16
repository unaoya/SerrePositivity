module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.SmallParameterClosure
public import SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneHomotopyLocalization

/-! # A small homotopy-equivalent subcomplex from an actual small domination

Closing the image of the dominating map under the whole homotopy retains
both inverse homotopies. No model structure or ambient smallness is used.
-/

@[expose] public section
universe v w uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.MonoidalCategory

namespace SerrePositivity.SimplicialModel.SmallDominatedSubcomplex
variable {X K : SSet.{w}} (s : K ⟶ X) (q : X ⟶ K)
  (H : SSet.Homotopy (𝟙 X) (q ≫ s)) (A : X.Subcomplex)

abbrev complex : X.Subcomplex :=
  SmallParameterClosure.closure H.h (A ⊔ Subfunctor.range s)

lemma seed_le : A ≤ complex s q H A :=
  le_sup_left.trans (SmallParameterClosure.le_closure H.h _)

def inside : K ⟶ (complex s q H A).toSSet :=
  Subfunctor.lift s (le_sup_right.trans
    (SmallParameterClosure.le_closure H.h (A ⊔ Subfunctor.range s)))

lemma inside_inclusion : inside s q H A ≫ (complex s q H A).ι = s := rfl

def retraction : X ⟶ (complex s q H A).toSSet := q ≫ inside s q H A

lemma retraction_inclusion : retraction s q H A ≫ (complex s q H A).ι = q ≫ s := by
  rw [retraction, Category.assoc, inside_inclusion]

include H in
lemma small (hK : ∀ n, Small.{v} (K.obj n))
    (hA : SmallParameterClosure.IsSmall.{v} A) :
    SmallParameterClosure.IsSmall.{v} (complex s q H A) := by
  apply SmallParameterClosure.closure_small
  · intro n
    infer_instance
  · intro n
    have := hK n
    have := hA n
    change Small.{v} ↥(A.obj n ∪ Set.range (s.app n))
    infer_instance

/-- The same whole homotopy restricts to the countable closure. -/
def restrictedHomotopy : SSet.Homotopy (𝟙 (complex s q H A).toSSet)
    ((complex s q H A).ι ≫ retraction s q H A) where
  h := Subfunctor.lift ((complex s q H A).ι ▷ _ ≫ H.h)
    (SmallParameterClosure.closed H.h (A ⊔ Subfunctor.range s))
  h₀ := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    exact congrArg (fun f => f.app n x.val) H.h₀
  h₁ := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    exact congrArg (fun f => f.app n x.val) H.h₁
  rel := by
    apply NatTrans.ext
    funext n
    exact ConcreteCategory.hom_ext _ _ (fun x => False.elim x.1.property)

def inclusionImageIso {D : Type uD} [Category.{vD} D] (L : SSet.{w} ⥤ D)
    (hL : SSet.anodyneExtensions.IsInvertedBy L) : L.obj (complex s q H A).toSSet ≅ L.obj X where
  hom := L.map (complex s q H A).ι
  inv := L.map (retraction s q H A)
  hom_inv_id := (L.map_comp _ _).symm.trans
    ((AnodyneHomotopy.map_homotopy_eq L hL (restrictedHomotopy s q H A)).symm.trans
      (L.map_id _))
  inv_hom_id := by
    rw [← L.map_comp, retraction_inclusion]
    exact (AnodyneHomotopy.map_homotopy_eq L hL H).symm.trans (L.map_id _)

end SerrePositivity.SimplicialModel.SmallDominatedSubcomplex
