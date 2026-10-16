module
public import SerrePositivity.DifferentialGraded.Quotient.Identity
public import SerrePositivity.DifferentialGraded.Quotient.InternalRightUnit
public import SerrePositivity.DifferentialGraded.Complexes.RightUnitorEvaluation

/-! # 最終Hom合成の右単位 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma quotientComposition_right_unit (S : Set D) (x y : D) :
    (ρ_ (quotientHom A D S x y)).inv ≫ quotientHom A D S x y ◁ quotientIdentity A D S y ≫
      quotientComposition A D S x y y = 𝟙 _ := by
  apply chain_ext_apply
  intro n a
  simp only [chain_comp_apply]
  rw [complexRightUnitor_inv_apply, whiskerLeft_apply, quotientComposition_f, quotientIdentity_f]
  have h := congrArg (fun f : internalHom A D S x y ⟶ internalHom A D S x y => f.f n a)
    (internalComposition_right_unit A D S x y)
  change (internalComposition A D S x y y).f n
    ((internalHom A D S x y ◁ internalIdentity A D S y).f n
      ((ρ_ (internalHom A D S x y)).inv.f n a)) = a at h
  rw [complexRightUnitor_inv_apply, whiskerLeft_apply] at h
  exact h

end SerrePositivity.DifferentialGraded.DGQuotient
