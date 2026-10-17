module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.AppendRightPrepend
public import SerrePositivity.DifferentialGraded.Complexes.TensorCoproductExt

/-! # 任意次数cell path：CompositionPrepend -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (I : Type w) [Small.{u} I]
variable (C : Family A D I)

lemma internalComposition_prepend (x y z t : D) :
    (C.internalPrepend A D I x y z ▷ C.internalHom A D I z t) ≫ C.internalComposition A D I x z t =
    (α_ (homObject A D x y) (C.internalHom A D I y z) (C.internalHom A D I z t)).hom ≫
      (homObject A D x y) ◁ C.internalComposition A D I y z t ≫ C.internalPrepend A D I x y t := by
  apply tensorLeftRightCoproduct_hom_ext (homObject A D x y) (C.internalHom A D I z t)
    (fun w : List I => C.term A D I w y z)
  intro w
  let s : (homObject A D x y ⊗ C.term A D I w y z) ⊗ C.internalHom A D I z t ⟶
      (homObject A D x y ⊗ C.internalHom A D I y z) ⊗ C.internalHom A D I z t :=
    ((homObject A D x y) ◁ C.inclusion A D I w y z) ▷ C.internalHom A D I z t
  change s ≫ (C.internalPrepend A D I x y z ▷ C.internalHom A D I z t) ≫
      C.internalComposition A D I x z t =
    s ≫ (α_ (homObject A D x y) (C.internalHom A D I y z) (C.internalHom A D I z t)).hom ≫
      (homObject A D x y) ◁ C.internalComposition A D I y z t ≫ C.internalPrepend A D I x y t
  have hl : (((homObject A D x y) ◁ C.inclusion A D I w y z) ▷ C.internalHom A D I z t) ≫
      (C.internalPrepend A D I x y z ▷ C.internalHom A D I z t) ≫
      C.internalComposition A D I x z t =
    (C.prependMap A D I w x y z ▷ C.internalHom A D I z t) ≫ C.appendRight A D I w x z t := by
    rw [← comp_whiskerRight_assoc, internalPrepend_inclusion, comp_whiskerRight,
      Category.assoc, internalComposition_left_inclusion]
  have hm : (((homObject A D x y) ◁ C.inclusion A D I w y z) ▷ C.internalHom A D I z t) ≫
      (α_ (homObject A D x y) (C.internalHom A D I y z) (C.internalHom A D I z t)).hom ≫
      (homObject A D x y) ◁ C.internalComposition A D I y z t =
    (α_ (homObject A D x y) (C.term A D I w y z) (C.internalHom A D I z t)).hom ≫
      (homObject A D x y) ◁ C.appendRight A D I w y z t := by
    rw [associator_naturality_middle_assoc, ← whiskerLeft_comp, internalComposition_left_inclusion]
  have hr := congrArg (fun f => f ≫ C.internalPrepend A D I x y t) hm
  simpa only [Category.assoc] using hl.trans ((C.appendRight_prepend A D I w x y z t).trans hr.symm)

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
