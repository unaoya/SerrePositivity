module
public import SerrePositivity.DifferentialGraded.Quotient.CompositionDifferential

/-! # 最終合成の純tensor上の直接評価 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma quotientComposition_apply (S : Set D) (x y z : D) (p q n : ℤ) (hn : p + q = n)
    (a : (quotientHom A D S x y).X p) (b : (quotientHom A D S y z).X q) :
    (quotientComposition A D S x y z).f n
      (ιTensorObj (quotientHom A D S x y) (quotientHom A D S y z) p q n hn (a ⊗ₜ[A] b)) =
    (internalComposition A D S x y z).f n
      (ιTensorObj (internalHom A D S x y) (internalHom A D S y z) p q n hn (a ⊗ₜ[A] b)) :=
  ConcreteCategory.congr_hom (quotientComposition_ι A D S x y z p q n hn) (a ⊗ₜ[A] b)

end SerrePositivity.DifferentialGraded.DGQuotient
