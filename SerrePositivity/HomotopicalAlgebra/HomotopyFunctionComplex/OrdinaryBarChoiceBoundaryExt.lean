module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarChoiceTriangleGluing

/-! # Boundary choices are determined by their entire facet restrictions

This is joint faithfulness of the family of boundary restrictions. It does
not assert faithfulness of any individual restriction or base projection.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarChoiceBoundaryExt
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

lemma hom_ext {P : SSet.{max u v}} {n : ℕ}
    {X Y : OrdinaryBarChoiceCategory.Object (C := C) hcof hfib
      (P ⊗ (SSet.boundary (n + 1)).toSSet)} (a b : X ⟶ Y)
    (h : ∀ k : Fin (n + 2),
      (OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ SSet.boundary.ι k)).map a =
        (OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ SSet.boundary.ι k)).map b) : a = b := by
  have hb := congrArg OrdinaryBarChoiceCategory.Hom.base (h 0)
  change a.base = b.base at hb
  cases a with | mk f s =>
    cases b with | mk g t =>
      dsimp only at hb
      subst g
      have he : s = t := by
        apply BoundaryTensorGluing.hom_ext
        intro k
        have hk := OrdinaryBarFreeDiagramHomotopy.extension_eq hcof hfib _ _ (h k) rfl
        simpa only [OrdinaryBarChoiceTriangleGluing.reindex_extension,
          OrdinaryBarChoiceTriangleGluing.relabel_refl, Category.comp_id] using hk
      subst t
      rfl

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarChoiceBoundaryExt
