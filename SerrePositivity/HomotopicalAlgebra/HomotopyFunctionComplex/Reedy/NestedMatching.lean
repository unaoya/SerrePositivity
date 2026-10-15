module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.IndexReedy
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.Induced
public import Mathlib.CategoryTheory.Equivalence

/-! # Matching indices inside matching indices

Composition identifies the matching index at the target of an inverse map
with the matching index at that map in the inverse boundary category.
-/

@[expose] public section
universe v u t
noncomputable section
open CategoryTheory HomotopicalAlgebra

namespace SerrePositivity.Reedy
variable {J : Type u} [Category.{v} J] {inverse direct : MorphismProperty J}
  [inverse.IsMultiplicative] [direct.IsMultiplicative]
  {α : Type t} [LinearOrder α] [OrderBot α] [SuccOrder α] [WellFoundedLT α]
  (r : ReedyStructure inverse direct α) {j : J} (g : MatchingIndex r j)

abbrev matchingComposite (h : MatchingIndex r g.obj.right) : MatchingIndex r j :=
  ⟨Under.mk (g.obj.hom ≫ h.obj.hom), inverse.comp_mem _ _ g.property.1 h.property.1,
    fun hi ↦ by
      have he := congrArg r.deg (identities_endpoints _ hi)
      exact (ne_of_lt ((matching_degree_lt r h).trans (matching_degree_lt r g))) he.symm⟩

abbrev matchingCompositionMap (h : MatchingIndex r g.obj.right) :
    g ⟶ matchingComposite r g h :=
  ObjectProperty.homMk (Under.homMk h.obj.hom rfl)

abbrev matchingCompositionFunctor : MatchingIndex r g.obj.right ⥤ MatchingIndex r j where
  obj := matchingComposite r g
  map φ := ObjectProperty.homMk (Under.homMk φ.hom.right (by
    change (g.obj.hom ≫ _) ≫ _ = g.obj.hom ≫ _
    rw [Category.assoc, Under.w]))

abbrev matchingNestedFunctor : MatchingIndex r g.obj.right ⥤
    MatchingIndex (matchingReedy r j) g where
  obj h := ⟨Under.mk (matchingCompositionMap r g h), trivial, fun hi ↦ by
    have he := congrArg (fun x : MatchingIndex r j ↦ r.deg x.obj.right)
      (identities_endpoints _ hi)
    exact (ne_of_lt (matching_degree_lt r h)) he.symm⟩
  map φ := ObjectProperty.homMk (Under.homMk
    ((matchingCompositionFunctor r g).map φ) (by
      apply ObjectProperty.hom_ext
      apply Under.UnderMorphism.ext
      exact Under.w φ.hom))

def matchingNestedFullyFaithful : (matchingNestedFunctor r g).FullyFaithful where
  preimage φ := ObjectProperty.homMk (Under.homMk φ.hom.right.hom.right (by
    exact congrArg (fun f ↦ f.hom.right) (Under.w φ.hom)))
  map_preimage φ := by
    apply ObjectProperty.hom_ext
    apply Under.UnderMorphism.ext
    apply ObjectProperty.hom_ext
    apply Under.UnderMorphism.ext
    rfl
  preimage_map φ := by
    apply ObjectProperty.hom_ext
    apply Under.UnderMorphism.ext
    rfl

abbrev matchingUnnest (n : MatchingIndex (matchingReedy r j) g) :
    MatchingIndex r g.obj.right :=
  ⟨Under.mk n.obj.hom.hom.right, matching_map_inverse r n.obj.hom,
    fun hi ↦ n.property.2 (fullSubcategory_identities n.obj.hom
      (CommaIdentities.under_reflect n.obj.hom.hom hi))⟩

lemma matchingComposite_unnest (n : MatchingIndex (matchingReedy r j) g) :
    matchingComposite r g (matchingUnnest r g n) = n.obj.right := by
  apply ObjectProperty.FullSubcategory.ext
  change Under.mk (g.obj.hom ≫ n.obj.hom.hom.right) = n.obj.right.obj
  rw [Under.w]
  rfl

def matchingNestedCounit (n : MatchingIndex (matchingReedy r j) g) :
    (matchingNestedFunctor r g).obj (matchingUnnest r g n) ≅ n := by
  let he := matchingComposite_unnest r g n
  apply ObjectProperty.isoMk _
  apply Under.isoMk (eqToIso he)

instance matchingNested_full : (matchingNestedFunctor r g).Full :=
  (matchingNestedFullyFaithful r g).full

instance matchingNested_faithful : (matchingNestedFunctor r g).Faithful :=
  (matchingNestedFullyFaithful r g).faithful

instance matchingNested_essSurj : (matchingNestedFunctor r g).EssSurj where
  mem_essImage n := ⟨matchingUnnest r g n, ⟨matchingNestedCounit r g n⟩⟩

instance matchingNested_isEquivalence : (matchingNestedFunctor r g).IsEquivalence where

abbrev matchingNestedEquivalence : MatchingIndex r g.obj.right ≌
    MatchingIndex (matchingReedy r j) g := (matchingNestedFunctor r g).asEquivalence

lemma matchingNested_target : (matchingNestedEquivalence r g).functor ⋙
    matchingTarget (matchingReedy r j) g ⋙ matchingTarget r j =
      matchingTarget r g.obj.right := rfl

end SerrePositivity.Reedy
