module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.SimplexIndexFinite
public import Mathlib.AlgebraicTopology.SimplicialSet.Degenerate
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-! # Nonempty inverse boundaries have the nondegenerate core as a terminal object

The core is constructed from any inverse quotient and the proved unique
nondegenerate decomposition. All other inverse quotients factor uniquely
through that same core. The whole simplex category can be large.
-/

@[expose] public section
universe w vC uC
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Reedy

namespace SerrePositivity.SimplicialModel.SimplexMatchingTerminal
variable (X : SSet.{w}) (s : X.Elementsᵒᵖ)

abbrev dimension (s : X.Elementsᵒᵖ) := s.unop.obj.unop.len
abbrev operator {a b : X.Elementsᵒᵖ} (f : a ⟶ b) := f.unop.hom.unop
abbrev Index := MatchingIndex (SimplexIndexFinite.reedy X) s

structure Core where
  dim : ℕ
  simplex : X.nonDegenerate dim
  map : s.unop.obj.unop ⟶ SimplexCategory.mk dim
  epi : Epi map
  relation : X.map map.op simplex.val = s.unop.val
  smaller : dim < dimension X s

attribute [instance] Core.epi

/-- Start with any proper inverse quotient and reduce its target to a nondegenerate simplex. -/
def coreOf (q : Index X s) : Core X s := by
  apply Classical.choice
  have : Epi (operator X q.obj.hom) := q.property.1
  obtain ⟨m, π, hπ, y, hy⟩ := X.exists_nonDegenerate q.obj.right.unop.val
  refine ⟨⟨m, y, operator X q.obj.hom ≫ π, inferInstance, ?_, ?_⟩⟩
  · change X.map (π.op ≫ (operator X q.obj.hom).op) y.val = s.unop.val
    rw [Functor.map_comp]
    change X.map (operator X q.obj.hom).op (X.map π.op y.val) = s.unop.val
    rw [← hy]
    exact q.obj.hom.unop.map_val
  · exact lt_of_le_of_lt (SimplexCategory.len_le_of_epi π)
      (matching_degree_lt (SimplexIndexFinite.reedy X) q)

lemma degree_eq_of_identities {a b : X.Elementsᵒᵖ} (f : a ⟶ b)
    (h : MorphismProperty.identities X.Elementsᵒᵖ f) : dimension X a = dimension X b := by
  cases h
  rfl

namespace Core
variable {X s} (c : Core X s)

abbrev target : X.Elementsᵒᵖ :=
  Opposite.op (X.elementsMk (Opposite.op (SimplexCategory.mk c.dim)) c.simplex.val)
abbrev arrow : s ⟶ c.target := (Functor.Elements.homMk c.map.op c.relation).op

abbrev object : Index X s :=
  ⟨Under.mk c.arrow, c.epi, fun h => by
    have hd : dimension X s = c.dim := degree_eq_of_identities X c.arrow h
    exact c.smaller.ne hd.symm⟩

end Core

lemma matchingHom_ext (q q' : Index X s) (f g : q ⟶ q') : f = g := by
  have : Epi (operator X q.obj.hom) := q.property.1
  apply ObjectProperty.hom_ext
  apply Under.UnderMorphism.ext
  apply Quiver.Hom.unop_inj
  apply Functor.Elements.hom_ext
  apply Quiver.Hom.unop_inj
  apply (cancel_epi (operator X q.obj.hom)).mp
  exact (congrArg (fun f => f.unop.hom.unop) (Under.w f.hom)).trans
    (congrArg (fun f => f.unop.hom.unop) (Under.w g.hom)).symm

instance matchingHom_subsingleton (q q' : Index X s) : Subsingleton (q ⟶ q') :=
  ⟨matchingHom_ext X s q q'⟩

/-- Each actual quotient factors through the specified nondegenerate core. -/
def toCore (c : Core X s) (q : Index X s) : q ⟶ c.object := by
  apply Classical.choice
  have : Epi (operator X q.obj.hom) := q.property.1
  obtain ⟨m, π, hπ, y, hy⟩ := X.exists_nonDegenerate q.obj.right.unop.val
  have hr : s.unop.val = X.map (operator X q.obj.hom ≫ π).op y.val := by
    change s.unop.val = X.map (π.op ≫ (operator X q.obj.hom).op) y.val
    rw [Functor.map_comp]
    change s.unop.val = X.map (operator X q.obj.hom).op (X.map π.op y.val)
    rw [← hy]
    exact q.obj.hom.unop.map_val.symm
  have hm := X.unique_nonDegenerate_dim s.unop.val c.map c.simplex c.relation.symm
    (operator X q.obj.hom ≫ π) y hr
  subst m
  have hs := X.unique_nonDegenerate_simplex s.unop.val c.map c.simplex c.relation.symm
    (operator X q.obj.hom ≫ π) y hr
  have hmap := X.unique_nonDegenerate_map s.unop.val c.map c.simplex c.relation.symm
    (operator X q.obj.hom ≫ π) y hr
  have he : X.map π.op c.simplex.val = q.obj.right.unop.val := by
    rw [congrArg Subtype.val hs]
    exact hy.symm
  refine ⟨ObjectProperty.homMk (Under.homMk
    (Functor.Elements.homMk (x := c.target.unop) (y := q.obj.right.unop) π.op he).op ?_)⟩
  apply Quiver.Hom.unop_inj
  exact Functor.Elements.hom_ext (congrArg Quiver.Hom.op hmap.symm)

def coreIsTerminal (c : Core X s) : IsTerminal c.object :=
  IsTerminal.ofUniqueHom (toCore X s c) (fun _ _ => Subsingleton.elim _ _)

/-- Every nonempty inverse boundary has an actual terminal nondegenerate quotient. -/
lemma exists_terminal [Nonempty (Index X s)] : ∃ q : Index X s, Nonempty (IsTerminal q) :=
  ⟨(coreOf X s (Classical.choice inferInstance)).object,
    ⟨coreIsTerminal X s (coreOf X s (Classical.choice inferInstance))⟩⟩

lemma index_isEmpty_of_nonDegenerate
    (hs : s.unop.val ∈ X.nonDegenerate (dimension X s)) : IsEmpty (Index X s) := by
  refine ⟨fun q => ?_⟩
  have : Epi (operator X q.obj.hom) := q.property.1
  have : IsIso (operator X q.obj.hom) :=
    X.isIso_of_nonDegenerate ⟨s.unop.val, hs⟩ (operator X q.obj.hom)
      q.obj.right.unop.val q.obj.hom.unop.map_val
  have he := SimplexCategory.len_eq_of_isIso (operator X q.obj.hom)
  exact (matching_degree_lt (SimplexIndexFinite.reedy X) q).ne he.symm

variable {C : Type uC} [Category.{vC} C] [HasFiniteLimits C]

/-- On a nonempty inverse boundary, inverting all degeneracies makes matching an isomorphism. -/
lemma matchingComparison_isIso (A : X.Elementsᵒᵖ ⥤ C)
    (hA : ∀ {a b : X.Elementsᵒᵖ} (f : a ⟶ b),
      (elementsDirect (direct := simplexInverse.op) X).op f → IsIso (A.map f))
    [Nonempty (Index X s)] :
    IsIso ((matchingComparison (SimplexIndexFinite.reedy X) s).app A) := by
  obtain ⟨q, ⟨hq⟩⟩ := exists_terminal X s
  let H := matchingTarget (SimplexIndexFinite.reedy X) s ⋙ A
  let : ∀ (q q' : Index X s) (f : q ⟶ q'), IsIso (H.map f) :=
    fun _ _ f => hA f.hom.right (matching_map_inverse (SimplexIndexFinite.reedy X) f)
  have : IsIso (limit.π H q) := isIso_π_of_isTerminal hq H
  have hf : (matchingComparison (SimplexIndexFinite.reedy X) s).app A ≫ limit.π H q =
      A.map q.obj.hom := limit.lift_π _ _
  have : IsIso ((matchingComparison (SimplexIndexFinite.reedy X) s).app A ≫ limit.π H q) := by
    rw [hf]
    exact hA q.obj.hom q.property.1
  exact IsIso.of_isIso_comp_right _ (limit.π H q)

end SerrePositivity.SimplicialModel.SimplexMatchingTerminal
