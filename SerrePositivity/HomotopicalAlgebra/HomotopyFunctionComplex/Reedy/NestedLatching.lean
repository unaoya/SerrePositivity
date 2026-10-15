module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.IndexReedy
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.Induced
public import Mathlib.CategoryTheory.Equivalence

/-! # Latching indices inside latching indices

Composition identifies the latching index at the source of a direct map
with the latching index at that map in the direct boundary category.
-/

@[expose] public section
universe v u t
noncomputable section
open CategoryTheory HomotopicalAlgebra

namespace SerrePositivity.Reedy
variable {J : Type u} [Category.{v} J] {inverse direct : MorphismProperty J}
  [inverse.IsMultiplicative] [direct.IsMultiplicative]
  {α : Type t} [LinearOrder α] [OrderBot α] [SuccOrder α] [WellFoundedLT α]
  (r : ReedyStructure inverse direct α) {j : J} (g : LatchingIndex r j)

abbrev latchingComposite (h : LatchingIndex r g.obj.left) : LatchingIndex r j :=
  ⟨Over.mk (h.obj.hom ≫ g.obj.hom), direct.comp_mem _ _ h.property.1 g.property.1,
    fun hi ↦ by
      have he := congrArg r.deg (identities_endpoints _ hi)
      exact (ne_of_lt ((latching_degree_lt r h).trans (latching_degree_lt r g))) he⟩

abbrev latchingCompositionMap (h : LatchingIndex r g.obj.left) :
    latchingComposite r g h ⟶ g :=
  ObjectProperty.homMk (Over.homMk h.obj.hom rfl)

abbrev latchingCompositionFunctor : LatchingIndex r g.obj.left ⥤ LatchingIndex r j where
  obj := latchingComposite r g
  map φ := ObjectProperty.homMk (Over.homMk φ.hom.left (by
    change _ ≫ (_ ≫ g.obj.hom) = _ ≫ g.obj.hom
    rw [← Category.assoc, Over.w]))

abbrev latchingNestedFunctor : LatchingIndex r g.obj.left ⥤
    LatchingIndex (latchingReedy r j) g where
  obj h := ⟨Over.mk (latchingCompositionMap r g h), trivial, fun hi ↦ by
    have he := congrArg (fun x : LatchingIndex r j ↦ r.deg x.obj.left)
      (identities_endpoints _ hi)
    exact (ne_of_lt (latching_degree_lt r h)) he⟩
  map φ := ObjectProperty.homMk (Over.homMk
    ((latchingCompositionFunctor r g).map φ) (by
      apply ObjectProperty.hom_ext
      apply Over.OverMorphism.ext
      exact Over.w φ.hom))

def latchingNestedFullyFaithful : (latchingNestedFunctor r g).FullyFaithful where
  preimage φ := ObjectProperty.homMk (Over.homMk φ.hom.left.hom.left (by
    exact congrArg (fun f ↦ f.hom.left) (Over.w φ.hom)))
  map_preimage φ := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    rfl
  preimage_map φ := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    rfl

abbrev latchingUnnest (n : LatchingIndex (latchingReedy r j) g) :
    LatchingIndex r g.obj.left :=
  ⟨Over.mk n.obj.hom.hom.left, latching_map_direct r n.obj.hom,
    fun hi ↦ n.property.2 (fullSubcategory_identities n.obj.hom
      (CommaIdentities.over_reflect n.obj.hom.hom hi))⟩

lemma latchingComposite_unnest (n : LatchingIndex (latchingReedy r j) g) :
    latchingComposite r g (latchingUnnest r g n) = n.obj.left := by
  apply ObjectProperty.FullSubcategory.ext
  change Over.mk (n.obj.hom.hom.left ≫ g.obj.hom) = n.obj.left.obj
  rw [Over.w]
  rfl

def latchingNestedCounit (n : LatchingIndex (latchingReedy r j) g) :
    (latchingNestedFunctor r g).obj (latchingUnnest r g n) ≅ n := by
  let he := latchingComposite_unnest r g n
  apply ObjectProperty.isoMk _
  apply Over.isoMk (eqToIso he)

instance latchingNested_full : (latchingNestedFunctor r g).Full :=
  (latchingNestedFullyFaithful r g).full

instance latchingNested_faithful : (latchingNestedFunctor r g).Faithful :=
  (latchingNestedFullyFaithful r g).faithful

instance latchingNested_essSurj : (latchingNestedFunctor r g).EssSurj where
  mem_essImage n := ⟨latchingUnnest r g n, ⟨latchingNestedCounit r g n⟩⟩

instance latchingNested_isEquivalence : (latchingNestedFunctor r g).IsEquivalence where

abbrev latchingNestedEquivalence : LatchingIndex r g.obj.left ≌
    LatchingIndex (latchingReedy r j) g := (latchingNestedFunctor r g).asEquivalence

lemma latchingNested_source : (latchingNestedEquivalence r g).functor ⋙
    latchingSource (latchingReedy r j) g ⋙ latchingSource r j =
      latchingSource r g.obj.left := rfl

end SerrePositivity.Reedy
