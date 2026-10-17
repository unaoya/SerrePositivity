module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.CompositionDifferential

/-! # cell付加の最終Hom合成：CompositionEvaluation -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (I : Type w) [Small.{u} I]
variable (C : Family A D I)

lemma attachedComposition_apply (x y z : D) (p q n : ℤ) (hn : p + q = n)
    (a : (C.attachedHom A D I x y).X p) (b : (C.attachedHom A D I y z).X q) :
    (C.attachedComposition A D I x y z).f n
      (ιTensorObj (C.attachedHom A D I x y) (C.attachedHom A D I y z) p q n hn (a ⊗ₜ[A] b)) =
    (C.internalComposition A D I x y z).f n
      (ιTensorObj (C.internalHom A D I x y) (C.internalHom A D I y z) p q n hn (a ⊗ₜ[A] b)) :=
  ConcreteCategory.congr_hom (C.attachedComposition_ι A D I x y z p q n hn) (a ⊗ₜ[A] b)

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
