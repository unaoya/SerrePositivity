module
public import SerrePositivity.DifferentialGraded.Quotient.CompositionPrefix
public import SerrePositivity.DifferentialGraded.Quotient.CompositionPrepend
public import SerrePositivity.DifferentialGraded.Complexes.TensorCarryAssociativity

/-! # 任意左pathと二つの全右pathの連結の結合則 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma appendRight_assoc {S : Set D} (w : Word S) (x y z t : D) :
    (appendRight A D w x y z ▷ internalHom A D S z t) ≫ internalComposition A D S x z t =
    (α_ (term A D w x y) (internalHom A D S y z) (internalHom A D S z t)).hom ≫
      (term A D w x y) ◁ internalComposition A D S y z t ≫ appendRight A D w x y t := by
  induction w generalizing x with
  | nil =>
    simpa only [appendRight_nil, term_nil] using internalComposition_prepend A D S x y z t
  | cons b w ih =>
    have he := tensorCarry_assoc (epsilonComplex A) (term A D w b.val y)
      (internalHom A D S y z) (internalHom A D S z t) (internalHom A D S b.val z)
      (internalHom A D S b.val t) (internalHom A D S y t)
      (appendRight A D w b.val y z) (internalComposition A D S b.val z t)
      (internalComposition A D S y z t) (appendRight A D w b.val y t) (ih b.val)
    have hk := tensorCarry_assoc (homObject A D x b.val)
      (epsilonComplex A ⊗ term A D w b.val y) (internalHom A D S y z)
      (internalHom A D S z t) (epsilonComplex A ⊗ internalHom A D S b.val z)
      (epsilonComplex A ⊗ internalHom A D S b.val t) (internalHom A D S y t)
      ((α_ (epsilonComplex A) (term A D w b.val y) (internalHom A D S y z)).hom ≫
        (epsilonComplex A) ◁ appendRight A D w b.val y z)
      ((α_ (epsilonComplex A) (internalHom A D S b.val z) (internalHom A D S z t)).hom ≫
        (epsilonComplex A) ◁ internalComposition A D S b.val z t)
      (internalComposition A D S y z t)
      ((α_ (epsilonComplex A) (term A D w b.val y) (internalHom A D S y t)).hom ≫
        (epsilonComplex A) ◁ appendRight A D w b.val y t) he
    have hp := congrArg (fun f => f ≫ prefixPath A D b x t) hk
    simp only [comp_whiskerRight, whiskerLeft_comp, Category.assoc] at hp
    rw [appendRight_cons]
    simp only [comp_whiskerRight, Category.assoc]
    rw [internalComposition_prefixPath]
    simpa only [appendRight_cons, term_cons, whiskerLeft_comp, comp_whiskerRight,
      Category.assoc] using hp

end SerrePositivity.DifferentialGraded.DGQuotient
