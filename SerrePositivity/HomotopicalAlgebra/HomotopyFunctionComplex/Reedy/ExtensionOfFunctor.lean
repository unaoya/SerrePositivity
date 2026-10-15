module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.ExtensionTransformation

/-! # Attaching data supplied by an existing diagram and natural transformation -/

@[expose] public section
universe v u t v' u'
noncomputable section
open CategoryTheory HomotopicalAlgebra

namespace SerrePositivity.Reedy.BoundaryExtension
variable {J : Type u} [Category.{v} J] {inverse direct : MorphismProperty J}
  [inverse.IsMultiplicative] [direct.IsMultiplicative]
  {α : Type t} [LinearOrder α] [OrderBot α] [SuccOrder α] [WellFoundedLT α]
  (r : ReedyStructure inverse direct α) (j : J)
  {C : Type u'} [Category.{v'} C]

abbrev ofFunctor (F : J ⥤ C) : BoundaryExtension r j (lowerInclusion r (r.deg j) ⋙ F) where
  obj := F.obj j
  incoming f _ := F.map f
  outgoing f _ := F.map f
  incoming_naturality f g _ _ := (F.map_comp f.hom g).symm
  outgoing_naturality f g _ _ := (F.map_comp f g.hom).symm
  crossing f g _ _ := (F.map_comp f g).symm

abbrev mapOfNatTrans {F G : J ⥤ C} (τ : F ⟶ G) :
    Map (ofFunctor r j F) (ofFunctor r j G)
      (Functor.whiskerLeft (lowerInclusion r (r.deg j)) τ) where
  hom := τ.app j
  incoming f _ := τ.naturality f
  outgoing f _ := τ.naturality f

end SerrePositivity.Reedy.BoundaryExtension
