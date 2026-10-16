module
public import SerrePositivity.DifferentialGraded.Quotient.InternalAssociativity
public import SerrePositivity.DifferentialGraded.Quotient.RightIdentity
public import SerrePositivity.DifferentialGraded.Quotient.CompositionEvaluation
public import SerrePositivity.DifferentialGraded.Complexes.TensorCompositionAssociativity

/-! # 最終Hom合成の結合則 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma quotientComposition_assoc (S : Set D) (x y z t : D) :
    (quotientComposition A D S x y z ▷ quotientHom A D S z t) ≫
      quotientComposition A D S x z t =
    (α_ (quotientHom A D S x y) (quotientHom A D S y z) (quotientHom A D S z t)).hom ≫
      quotientHom A D S x y ◁ quotientComposition A D S y z t ≫
        quotientComposition A D S x y t := by
  apply tensorComposition_assoc_of_apply
  intro p q r n hn a b c
  simp only [quotientComposition_apply]
  exact tensorComposition_assoc_apply
    (internalHom A D S x y) (internalHom A D S y z) (internalHom A D S z t)
    (internalHom A D S x z) (internalHom A D S y t) (internalHom A D S x t)
    (internalComposition A D S x y z) (internalComposition A D S x z t)
    (internalComposition A D S y z t) (internalComposition A D S x y t)
    (internalComposition_assoc A D S x y z t) p q r n hn a b c

end SerrePositivity.DifferentialGraded.DGQuotient
