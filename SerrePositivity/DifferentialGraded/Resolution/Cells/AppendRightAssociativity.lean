module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.CompositionPrefix
public import SerrePositivity.DifferentialGraded.Resolution.Cells.CompositionPrepend
public import SerrePositivity.DifferentialGraded.Complexes.TensorCarryAssociativity

/-! # 任意次数cell path：AppendRightAssociativity -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (I : Type w) [Small.{u} I]
variable (C : Family A D I)

lemma appendRight_assoc (w : List I) (x y z t : D) :
    (C.appendRight A D I w x y z ▷ C.internalHom A D I z t) ≫ C.internalComposition A D I x z t =
    (α_ (C.term A D I w x y) (C.internalHom A D I y z) (C.internalHom A D I z t)).hom ≫
      (C.term A D I w x y) ◁ C.internalComposition A D I y z t ≫ C.appendRight A D I w x y t := by
  induction w generalizing x with
  | nil =>
    simpa only [internalPrepend, term] using C.internalComposition_prepend A D I x y z t
  | cons b w ih =>
    have he := tensorCarry_assoc (C.generator A D I b) (C.term A D I w (C.target b) y)
      (C.internalHom A D I y z) (C.internalHom A D I z t) (C.internalHom A D I (C.target b) z)
      (C.internalHom A D I (C.target b) t) (C.internalHom A D I y t)
      (C.appendRight A D I w (C.target b) y z) (C.internalComposition A D I (C.target b) z t)
      (C.internalComposition A D I y z t) (C.appendRight A D I w (C.target b) y t) (ih (C.target b))
    have hk := tensorCarry_assoc (homObject A D x (C.source b))
      (C.generator A D I b ⊗ C.term A D I w (C.target b) y) (C.internalHom A D I y z)
      (C.internalHom A D I z t) (C.generator A D I b ⊗ C.internalHom A D I (C.target b) z)
      (C.generator A D I b ⊗ C.internalHom A D I (C.target b) t) (C.internalHom A D I y t)
      ((α_ (C.generator A D I b) (C.term A D I w (C.target b) y) (C.internalHom A D I y z)).hom ≫
        (C.generator A D I b) ◁ C.appendRight A D I w (C.target b) y z)
      ((α_ (C.generator A D I b) (C.internalHom A D I (C.target b) z) (C.internalHom A D I z t)).hom
        ≫
        (C.generator A D I b) ◁ C.internalComposition A D I (C.target b) z t)
      (C.internalComposition A D I y z t)
      ((α_ (C.generator A D I b) (C.term A D I w (C.target b) y) (C.internalHom A D I y t)).hom ≫
        (C.generator A D I b) ◁ C.appendRight A D I w (C.target b) y t) he
    have hp := congrArg (fun f => f ≫ C.prefixPath A D I b x t) hk
    simp only [comp_whiskerRight, whiskerLeft_comp, Category.assoc] at hp
    rw [appendRight_cons]
    simp only [comp_whiskerRight, Category.assoc]
    rw [internalComposition_prefixPath]
    simpa only [appendRight_cons, term, whiskerLeft_comp, comp_whiskerRight,
      Category.assoc] using hp

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
