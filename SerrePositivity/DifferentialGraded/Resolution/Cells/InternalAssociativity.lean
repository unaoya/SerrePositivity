module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.AppendRightAssociativity
public import SerrePositivity.DifferentialGraded.Complexes.TensorRightTwoCoproductExt

/-! # 任意次数cell path：InternalAssociativity -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (I : Type w) [Small.{u} I]
variable (C : Family A D I)

lemma internalComposition_assoc (x y z t : D) :
    (C.internalComposition A D I x y z ▷ C.internalHom A D I z t) ≫
      C.internalComposition A D I x z t =
    (α_ (C.internalHom A D I x y) (C.internalHom A D I y z) (C.internalHom A D I z t)).hom ≫
      C.internalHom A D I x y ◁ C.internalComposition A D I y z t ≫
        C.internalComposition A D I x y t := by
  apply tensorRightTwoCoproduct_hom_ext (fun w : List I => C.term A D I w x y)
    (C.internalHom A D I y z) (C.internalHom A D I z t) (C.internalHom A D I x t)
  intro w
  change ((C.inclusion A D I w x y ▷ C.internalHom A D I y z) ▷ C.internalHom A D I z t) ≫
      (C.internalComposition A D I x y z ▷ C.internalHom A D I z t) ≫
        C.internalComposition A D I x z t = _
  rw [← comp_whiskerRight_assoc, internalComposition_left_inclusion,
    associator_naturality_left_assoc, ← whisker_exchange_assoc]
  change (C.appendRight A D I w x y z ▷ C.internalHom A D I z t) ≫
      C.internalComposition A D I x z t =
    (α_ (C.term A D I w x y) (C.internalHom A D I y z) (C.internalHom A D I z t)).hom ≫
      (C.term A D I w x y) ◁ C.internalComposition A D I y z t ≫
        (C.inclusion A D I w x y ▷ C.internalHom A D I y t) ≫ C.internalComposition A D I x y t
  rw [internalComposition_left_inclusion, appendRight_assoc]

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
