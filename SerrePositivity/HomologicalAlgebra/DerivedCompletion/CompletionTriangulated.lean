module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ComplexCompletionReflection
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.CategoryTheory.Triangulated.Adjunction

/-! # 実導来完備化は完全三角形を保つ

既存の実完備化の普遍性を、導来完備対象の充満部分圏への反映として用いる。
部分圏の三角構造は既存の導来完備性の閉性から得る。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] (a : R)

/-- 実導来圏で導来 a 完備である対象の性質。 -/
def completeProperty : ObjectProperty (ConcreteDerivedCategory R) := IsComplete R a

instance completeProperty_isClosedUnderIsomorphisms :
    (completeProperty R a).IsClosedUnderIsomorphisms where
  of_iso e hX := isComplete_of_iso R a e hX

instance completeProperty_isTriangulated : (completeProperty R a).IsTriangulated where
  exists_zero := ⟨0, isZero_zero _, by
    apply isComplete_of_scalar_pow_zero R a _ 0
    exact (isZero_zero _).eq_of_src _ _⟩
  isStableUnderShiftBy n := ⟨fun X hX => isComplete_shift R a hX n⟩
  ext₂' T hT h₁ h₃ :=
    (completeProperty R a).le_isoClosure _ (isComplete_triangle_middle R a T hT h₁ h₃)

/-- 既存の実完備化を導来完備対象の充満部分圏へ持ち上げる。 -/
def completeReflector : ConcreteDerivedCategory R ⥤ (completeProperty R a).FullSubcategory :=
  (completeProperty R a).lift (derivedComplexCompletionFunctor R a)
    (derivedComplexCompletionFunctor_isComplete R a)

/-- 元の完備化単位による Hom の普遍性から得る反映の随伴。 -/
def completeReflectorAdjunction : completeReflector R a ⊣ (completeProperty R a).ι :=
  Adjunction.mkOfHomEquiv
    { homEquiv X Y :=
        ((completeProperty R a).fullyFaithfulι.homEquiv.trans
          (derivedComplexCompletionHomEquiv R a X Y.obj Y.property))
      homEquiv_naturality_left_symm := by
        intro X' X Y f g
        apply InducedCategory.hom_ext
        apply (derivedComplexCompletionHomEquiv R a X' Y.obj Y.property).injective
        change (derivedComplexCompletionHomEquiv R a X' Y.obj Y.property)
            ((derivedComplexCompletionHomEquiv R a X' Y.obj Y.property).symm (f ≫ g)) =
          (derivedComplexCompletionUnit R a).app X' ≫
            ((derivedComplexCompletionFunctor R a).map f ≫
              (derivedComplexCompletionHomEquiv R a X Y.obj Y.property).symm g)
        rw [Equiv.apply_symm_apply]
        rw [← Category.assoc, ← (derivedComplexCompletionUnit R a).naturality f]
        simp only [Functor.id_map, Category.assoc]
        exact congrArg (fun k => f ≫ k)
          ((derivedComplexCompletionHomEquiv R a X Y.obj Y.property).apply_symm_apply g).symm
      homEquiv_naturality_right := by
        intro X Y Y' f g
        change (derivedComplexCompletionUnit R a).app X ≫ (f.hom ≫ g.hom) =
          ((derivedComplexCompletionUnit R a).app X ≫ f.hom) ≫ g.hom
        exact (Category.assoc _ _ _).symm }

instance completeReflector_commShift : (completeReflector R a).CommShift ℤ :=
  (completeReflectorAdjunction R a).leftAdjointCommShift ℤ

instance completeReflectorAdjunction_commShift : (completeReflectorAdjunction R a).CommShift ℤ :=
  (completeReflectorAdjunction R a).commShift_of_rightAdjoint ℤ

instance completeReflector_isTriangulated : (completeReflector R a).IsTriangulated :=
  (completeReflectorAdjunction R a).isTriangulated_leftAdjoint

instance derivedComplexCompletionFunctor_commShift :
    (derivedComplexCompletionFunctor R a).CommShift ℤ :=
  inferInstanceAs ((completeReflector R a ⋙ (completeProperty R a).ι).CommShift ℤ)

instance derivedComplexCompletionFunctor_isTriangulated :
    (derivedComplexCompletionFunctor R a).IsTriangulated :=
  inferInstanceAs ((completeReflector R a ⋙ (completeProperty R a).ι).IsTriangulated)

/-- 反映の随伴単位は、既存の実 Koszul 完備化の標準単位そのもの。 -/
theorem completeReflectorAdjunction_unit (X : ConcreteDerivedCategory R) :
    (completeReflectorAdjunction R a).unit.app X = (derivedComplexCompletionUnit R a).app X := by
  change (derivedComplexCompletionUnit R a).app X ≫ 𝟙 _ = _
  exact Category.comp_id _

end SerrePositivity.DerivedCompletion
