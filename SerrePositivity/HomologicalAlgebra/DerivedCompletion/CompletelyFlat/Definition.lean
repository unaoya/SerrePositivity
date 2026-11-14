module
public import SerrePositivity.HomologicalAlgebra.BoundedAboveDerivedBaseChange
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.CategoryTheory.Triangulated.TStructure.Basic
public import Mathlib.CategoryTheory.Shift.Basic
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.Basic.UnivLE
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.DerivedPurity
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionQuotient


import SerrePositivity.HomologicalAlgebra.NilpotentDerivedReduction
import SerrePositivity.HomologicalAlgebra.BaseChangeEquivalence

/-!
上に有界な導来対象の完全平坦性

可換環の実際の導来完備化と導来対象を用いる。
-/

public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

namespace SerrePositivity.BhattScholze.Prismatic

open CategoryTheory CategoryTheory.Limits HomologicalComplex DerivedCompletion
attribute [local instance] HasDerivedCategory.standard

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]

private def baseChangeCompositeIso (g : A →+* B) (h : B →+* C)
    (X : DerivedCategory.Minus (ModuleCat.{u} A)) :
    ((boundedAboveDerivedBaseChange h).obj ((boundedAboveDerivedBaseChange g).obj X)).obj ≅
      ((boundedAboveDerivedBaseChange (h.comp g)).obj X).obj :=
  boundedAboveDerivedBaseChangeModelIso h _
      (boundedAboveDerivedBaseChangeModel g X) ≪≫
    DerivedCategory.Q.mapIso (baseChangeCompIso g h (boundedAboveDerivedChosenModel X).complex) ≪≫
    (boundedAboveDerivedBaseChangeModelIso (h.comp g) X
      (boundedAboveDerivedChosenModel X)).symm

/-- 上に有界な導来対象の完全平坦性。標準剰余の離散性と零次ホモロジーの平坦性で表す。 -/
def IsDerivedCompletelyFlat (I : Ideal A) (X : DerivedCategory.Minus (ModuleCat.{u} A)) : Prop :=
  let Y := ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk I)).obj X).obj
  (∀ i : ℤ, i ≠ 0 → IsZero
    ((DerivedCategory.homologyFunctor (ModuleCat (A ⧸ I)) i).obj Y)) ∧
    Module.Flat (A ⧸ I) ((DerivedCategory.homologyFunctor (ModuleCat (A ⧸ I)) 0).obj Y)

end SerrePositivity.BhattScholze.Prismatic
