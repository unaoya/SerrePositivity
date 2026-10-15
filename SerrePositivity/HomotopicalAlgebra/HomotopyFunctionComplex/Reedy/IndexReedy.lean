module

public import SerrePositivity.CategoryTheory.CommaIdentities
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.OneSided
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.Subcategory

/-! # The inverse and direct Reedy structures on boundary index categories -/

@[expose] public section
universe v u t
open CategoryTheory HomotopicalAlgebra

namespace SerrePositivity.Reedy
variable {J : Type u} [Category.{v} J] {inverse direct : MorphismProperty J}
  [inverse.IsMultiplicative] [direct.IsMultiplicative]
  {α : Type t} [LinearOrder α] [OrderBot α] [SuccOrder α] [WellFoundedLT α]
  (r : ReedyStructure inverse direct α) (j : J)

abbrev matchingReedy : ReedyStructure (⊤ : MorphismProperty (MatchingIndex r j))
    (MorphismProperty.identities (MatchingIndex r j)) α :=
  inverseStructure (fun g ↦ r.deg g.obj.right) (fun φ hφ ↦
    r.lt₁ φ.hom.right (matching_map_inverse r φ) (fun h ↦
      hφ (fullSubcategory_identities φ (CommaIdentities.under_reflect φ.hom h))))

abbrev latchingReedy : ReedyStructure (MorphismProperty.identities (LatchingIndex r j))
    (⊤ : MorphismProperty (LatchingIndex r j)) α :=
  directStructure (fun f ↦ r.deg f.obj.left) (fun φ hφ ↦
    r.lt₂ φ.hom.left (latching_map_direct r φ) (fun h ↦
      hφ (fullSubcategory_identities φ (CommaIdentities.over_reflect φ.hom h))))

end SerrePositivity.Reedy
