module
public import SerrePositivity.DifferentialGraded.Quotient.CompositionComparison
public import SerrePositivity.DifferentialGraded.Quotient.InternalUnit

/-! # 最終Homの恒等射と合成の左単位 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 元の恒等射を最終Homへ入れた閉次数0の単位。 -/
def quotientIdentity (S : Set D) (x : D) : 𝟙_ (Complex A) ⟶ quotientHom A D S x x :=
  eId (Complex A) x ≫ originalHomInclusion A D S x x

lemma quotientIdentity_f (S : Set D) (x : D) (n : ℤ) :
    (quotientIdentity A D S x).f n = (internalIdentity A D S x).f n := rfl

lemma quotientComposition_left_unit (S : Set D) (x y : D) :
    (λ_ (quotientHom A D S x y)).inv ≫ quotientIdentity A D S x ▷ quotientHom A D S x y ≫
      quotientComposition A D S x x y = 𝟙 _ := by
  apply chain_ext_apply
  intro n a
  simp only [chain_comp_apply]
  rw [complexLeftUnitor_inv_apply, whiskerRight_apply, quotientComposition_f, quotientIdentity_f]
  have h := congrArg (fun f : internalHom A D S x y ⟶ internalHom A D S x y => f.f n a)
    (internalComposition_left_unit A D S x y)
  change (internalComposition A D S x x y).f n
    ((internalIdentity A D S x ▷ internalHom A D S x y).f n
      ((λ_ (internalHom A D S x y)).inv.f n a)) = a at h
  rw [complexLeftUnitor_inv_apply, whiskerRight_apply] at h
  exact h

end SerrePositivity.DifferentialGraded.DGQuotient
