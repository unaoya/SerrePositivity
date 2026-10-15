module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.BoundaryDiagram

/-! # Isomorphisms of Reedy attaching data

A lower natural isomorphism and an isomorphism on the attached objects,
compatible with incoming and outgoing maps, give an actual isomorphism in
the category of attaching diagrams. Compatibility of the inverse maps is
proved by cancelling the specified isomorphisms.
-/

@[expose] public section
universe v u t v' u'
noncomputable section
open CategoryTheory HomotopicalAlgebra

namespace SerrePositivity.Reedy.BoundaryDiagram
variable {J : Type u} [Category.{v} J] {inverse direct : MorphismProperty J}
  [inverse.IsMultiplicative] [direct.IsMultiplicative]
  {α : Type t} [LinearOrder α] [OrderBot α] [SuccOrder α] [WellFoundedLT α]
  {r : ReedyStructure inverse direct α} {j : J}
  {C : Type u'} [Category.{v'} C] {D E : BoundaryDiagram r j C}

abbrev isoMk (hl : D.lower ≅ E.lower) (hu : D.extension.obj ≅ E.extension.obj)
    (hin : ∀ {x : Lower r (r.deg j)} (f : x.obj ⟶ j) (hf : direct f),
      D.extension.incoming f hf ≫ hu.hom = hl.hom.app x ≫ E.extension.incoming f hf)
    (hout : ∀ {x : Lower r (r.deg j)} (f : j ⟶ x.obj) (hf : inverse f),
      D.extension.outgoing f hf ≫ hl.hom.app x = hu.hom ≫ E.extension.outgoing f hf) : D ≅ E where
  hom := ⟨hl.hom, { hom := hu.hom, incoming := hin, outgoing := hout }⟩
  inv :=
    ⟨hl.inv,
      { hom := hu.inv
        incoming := by
          intro x f hf
          apply (cancel_mono hu.hom).1
          rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc,
            hin f hf, ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
        outgoing := by
          intro x f hf
          apply (cancel_epi hu.hom).1
          rw [← Category.assoc, ← hout f hf, Category.assoc, Iso.hom_inv_id_app,
            Category.comp_id, Iso.hom_inv_id_assoc] }⟩
  hom_inv_id := by
    apply Hom.ext
    · exact hl.hom_inv_id
    · exact hu.hom_inv_id
  inv_hom_id := by
    apply Hom.ext
    · exact hl.inv_hom_id
    · exact hu.inv_hom_id

end SerrePositivity.Reedy.BoundaryDiagram
