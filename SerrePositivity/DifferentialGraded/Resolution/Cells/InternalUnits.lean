module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.AppendRecursion
public import SerrePositivity.DifferentialGraded.Complexes.TensorCarryUnit

/-! # cell pathの全直和上の合成の右単位 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory MonoidalCategory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (I : Type w) [Small.{u} I]
variable (C : Family A D I)

lemma appendRight_right_unit (w : List I) (x y : D) :
    (ρ_ (C.term A D I w x y)).inv ≫ C.term A D I w x y ◁ C.internalIdentity A D I y ≫
      C.appendRight A D I w x y y = C.inclusion A D I w x y := by
  induction w generalizing x with
  | nil =>
    change (ρ_ (homObject A D x y)).inv ≫
      homObject A D x y ◁ C.internalIdentity A D I y ≫ C.internalPrepend A D I x y y = _
    simp only [internalIdentity, originalHom, whiskerLeft_comp, Category.assoc]
    rw [internalPrepend_inclusion]
    simpa only [prependMap, originalHom] using
      e_comp_id_assoc (Complex A) x y (C.originalHom A D I x y)
  | cons b w ih =>
    have h := tensorCarry_right_unit (homObject A D x (C.source b))
      (C.generator A D I b ⊗ C.term A D I w (C.target b) y) (C.internalHom A D I y y)
      (C.generator A D I b ⊗ C.internalHom A D I (C.target b) y) (C.internalIdentity A D I y)
      ((α_ (C.generator A D I b) (C.term A D I w (C.target b) y) (C.internalHom A D I y y)).hom ≫
        (C.generator A D I b) ◁ C.appendRight A D I w (C.target b) y y)
    have ht := tensorCarry_right_unit (C.generator A D I b) (C.term A D I w (C.target b) y)
      (C.internalHom A D I y y) (C.internalHom A D I (C.target b) y) (C.internalIdentity A D I y)
      (C.appendRight A D I w (C.target b) y y)
    rw [ih (C.target b)] at ht
    rw [ht] at h
    have hp := congrArg (fun f => f ≫ C.prefixPath A D I b x y) h
    simp only [Category.assoc, prefixPath_inclusion] at hp
    simpa only [appendRight_cons, term, Category.assoc] using hp

lemma internalComposition_right_unit (x y : D) :
    (ρ_ (C.internalHom A D I x y)).inv ≫
      C.internalHom A D I x y ◁ C.internalIdentity A D I y ≫
      C.internalComposition A D I x y y = 𝟙 _ := by
  apply C.internalHom_ext A D I x y
  intro w
  simp only [Category.comp_id]
  rw [rightUnitor_inv_naturality_assoc, ← whisker_exchange_assoc,
    internalComposition_left_inclusion, appendRight_right_unit]

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
