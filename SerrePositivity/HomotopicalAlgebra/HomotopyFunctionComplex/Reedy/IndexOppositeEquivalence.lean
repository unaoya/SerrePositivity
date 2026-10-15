module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.IndexOpposite
public import Mathlib.CategoryTheory.Equivalence

/-! # Categorical opposite duality of Reedy boundary indices

The object correspondence is promoted to a fully faithful, essentially
surjective functor. The actual boundary source/target functors agree after
the equivalence. No limit or model-category assumptions are required.
-/

@[expose] public section
universe v u t
noncomputable section
open CategoryTheory HomotopicalAlgebra Opposite

namespace SerrePositivity.Reedy
variable {J : Type u} [Category.{v} J] {inverse direct : MorphismProperty J}
  [inverse.IsMultiplicative] [direct.IsMultiplicative]
  {α : Type t} [LinearOrder α] [OrderBot α] [SuccOrder α] [WellFoundedLT α]
  (r : ReedyStructure inverse direct α) (j : J)

def matchingOpFunctor : MatchingIndex r.op (op j) ⥤ (LatchingIndex r j)ᵒᵖ where
  obj f := op (matchingOpObjEquiv r j f)
  map φ := Quiver.Hom.op (ObjectProperty.homMk (Over.homMk φ.hom.right.unop (by
    exact congrArg Quiver.Hom.unop (Under.w φ.hom))))
  map_id f := by
    apply Quiver.Hom.unop_inj
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    rfl
  map_comp φ ψ := by
    apply Quiver.Hom.unop_inj
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    rfl

def matchingOpFullyFaithful : (matchingOpFunctor r j).FullyFaithful where
  preimage φ := ObjectProperty.homMk (Under.homMk φ.unop.hom.left.op (by
    exact congrArg Quiver.Hom.op (Over.w φ.unop.hom)))
  map_preimage φ := by
    apply Quiver.Hom.unop_inj
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    rfl
  preimage_map φ := by
    apply ObjectProperty.hom_ext
    apply Under.UnderMorphism.ext
    rfl

instance matchingOpFunctor_full : (matchingOpFunctor r j).Full :=
  (matchingOpFullyFaithful r j).full
instance matchingOpFunctor_faithful : (matchingOpFunctor r j).Faithful :=
  (matchingOpFullyFaithful r j).faithful
instance matchingOpFunctor_essSurj : (matchingOpFunctor r j).EssSurj where
  mem_essImage f := ⟨(matchingOpObjEquiv r j).symm f.unop,
    ⟨eqToIso (congrArg op ((matchingOpObjEquiv r j).apply_symm_apply f.unop))⟩⟩
instance matchingOpFunctor_isEquivalence : (matchingOpFunctor r j).IsEquivalence where

abbrev matchingOpEquivalence : MatchingIndex r.op (op j) ≌ (LatchingIndex r j)ᵒᵖ :=
  (matchingOpFunctor r j).asEquivalence

lemma matchingOpFunctor_target : matchingOpFunctor r j ⋙ (latchingSource r j).op =
    matchingTarget r.op (op j) := rfl

end SerrePositivity.Reedy
