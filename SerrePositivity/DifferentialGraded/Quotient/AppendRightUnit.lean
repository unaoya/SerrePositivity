module
public import SerrePositivity.DifferentialGraded.Quotient.AppendRight
public import SerrePositivity.DifferentialGraded.Quotient.InternalUnit
public import SerrePositivity.DifferentialGraded.Complexes.TensorCarryUnit

/-! # 全右pathへの連結の右単位 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 右側の空pathに恒等射を入れた連結は元のpath包含となる。 -/
lemma appendRight_right_unit {S : Set D} (w : Word S) (x y : D) :
    (ρ_ (term A D w x y)).inv ≫ term A D w x y ◁ internalIdentity A D S y ≫
      appendRight A D w x y y = ι A D S x y w := by
  induction w generalizing x with
  | nil =>
    rw [appendRight_nil]
    simp only [internalIdentity, term_nil, originalHom, whiskerLeft_comp, Category.assoc]
    rw [internalPrepend_ι]
    simpa only [prependMap_nil, originalHom] using
      e_comp_id_assoc (Complex A) x y (originalHom A D S x y)
  | cons b w ih =>
    have h := tensorCarry_right_unit (homObject A D x b.val)
      (epsilonComplex A ⊗ term A D w b.val y) (internalHom A D S y y)
      (epsilonComplex A ⊗ internalHom A D S b.val y) (internalIdentity A D S y)
      ((α_ (epsilonComplex A) (term A D w b.val y) (internalHom A D S y y)).hom ≫
        (epsilonComplex A) ◁ appendRight A D w b.val y y)
    have ht := tensorCarry_right_unit (epsilonComplex A) (term A D w b.val y)
      (internalHom A D S y y) (internalHom A D S b.val y) (internalIdentity A D S y)
      (appendRight A D w b.val y y)
    rw [ih b.val] at ht
    rw [ht] at h
    have hp := congrArg (fun f => f ≫ prefixPath A D b x y) h
    simp only [Category.assoc, prefixPath_ι] at hp
    simpa only [appendRight_cons, term_cons, Category.assoc] using hp

end SerrePositivity.DifferentialGraded.DGQuotient
