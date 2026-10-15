module

public import Mathlib.AlgebraicTopology.Reedy.Basic

/-! # Direct and inverse Reedy structures from strict degrees

When all nonidentity arrows strictly decrease (respectively increase)
degree, the normal factorization is the arrow followed by an identity
(respectively an identity followed by the arrow). Actual uniqueness of
factorization data is proved in both cases.
-/

@[expose] public section
universe v u t
open CategoryTheory HomotopicalAlgebra

namespace SerrePositivity.Reedy
variable {K : Type u} [Category.{v} K]
  {α : Type t} [LinearOrder α] [OrderBot α] [SuccOrder α] [WellFoundedLT α]

abbrev inverseStructure (degree : K → α)
    (hdegree : ∀ {x y : K} (f : x ⟶ y), ¬MorphismProperty.identities K f → degree y < degree x) :
    ReedyStructure (⊤ : MorphismProperty K) (MorphismProperty.identities K) α where
  deg := degree
  lt₁ f _ hf := hdegree f hf
  lt₂ _ hf hn := (hn hf).elim
  nonempty_unique {X Y} f := by
    exact ⟨{
      default := ⟨Y, f, 𝟙 Y, Category.comp_id _, trivial, MorphismProperty.ofHoms.mk Y⟩
      uniq := by
        rintro ⟨Z, i, p, fac, hi, hp⟩
        cases hp
        simp only [Category.comp_id] at fac
        subst i
        rfl }⟩

abbrev directStructure (degree : K → α)
    (hdegree : ∀ {x y : K} (f : x ⟶ y), ¬MorphismProperty.identities K f → degree x < degree y) :
    ReedyStructure (MorphismProperty.identities K) (⊤ : MorphismProperty K) α where
  deg := degree
  lt₁ _ hf hn := (hn hf).elim
  lt₂ f _ hf := hdegree f hf
  nonempty_unique {X Y} f := by
    exact ⟨{
      default := ⟨X, 𝟙 X, f, Category.id_comp _, MorphismProperty.ofHoms.mk X, trivial⟩
      uniq := by
        rintro ⟨Z, i, p, fac, hi, hp⟩
        cases hi
        simp only [Category.id_comp] at fac
        subst p
        rfl }⟩

end SerrePositivity.Reedy
