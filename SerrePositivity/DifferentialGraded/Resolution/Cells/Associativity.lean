module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.InternalAssociativity
public import SerrePositivity.DifferentialGraded.Resolution.Cells.RightIdentity
public import SerrePositivity.DifferentialGraded.Resolution.Cells.CompositionEvaluation
public import SerrePositivity.DifferentialGraded.Complexes.TensorCompositionAssociativity

/-! # cell付加の最終Hom合成：Associativity -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (I : Type w) [Small.{u} I]
variable (C : Family A D I)

lemma attachedComposition_assoc (x y z t : D) :
    (C.attachedComposition A D I x y z ▷ C.attachedHom A D I z t) ≫
      C.attachedComposition A D I x z t =
    (α_ (C.attachedHom A D I x y) (C.attachedHom A D I y z) (C.attachedHom A D I z t)).hom ≫
      C.attachedHom A D I x y ◁ C.attachedComposition A D I y z t ≫
        C.attachedComposition A D I x y t := by
  apply tensorComposition_assoc_of_apply
  intro p q r n hn a b c
  simp only [attachedComposition_apply]
  exact tensorComposition_assoc_apply
    (C.internalHom A D I x y) (C.internalHom A D I y z) (C.internalHom A D I z t)
    (C.internalHom A D I x z) (C.internalHom A D I y t) (C.internalHom A D I x t)
    (C.internalComposition A D I x y z) (C.internalComposition A D I x z t)
    (C.internalComposition A D I y z t) (C.internalComposition A D I x y t)
    (C.internalComposition_assoc A D I x y z t) p q r n hn a b c

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
