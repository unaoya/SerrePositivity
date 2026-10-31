module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionTriangulated
public import SerrePositivity.HomologicalAlgebra.BoundedAbove.Derived
public import SerrePositivity.HomologicalAlgebra.BoundedAboveDerivedBaseChange

/-! # 完備導来底変換の実完全三角形

始域・終域の比較と標準射の可換四角形から、第三対象の比較を構成する。
H⁰ だけを錐全体の比較の代用にはしない。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Pretriangulated
attribute [local instance] HasDerivedCategory.standard
variable {R B : Type u} [CommRing R] [CommRing B] (φ : R →+* B) (a : R)
variable {X Y Z : DerivedCategory.Minus (ModuleCat.{u} R)}
    (f : X ⟶ Y) (g : Y ⟶ Z) (δ : Z ⟶ X⟦(1 : ℤ)⟧)

/-- 元の全ての射を用いた、完備導来底変換後の三角形。 -/
def completedBaseChangeTriangle : Triangle (ConcreteDerivedCategory B) :=
  (derivedComplexCompletionFunctor B (φ a)).mapTriangle.obj
    (boundedAboveLeftDerivedTriangle (ModuleCat.extendScalars φ) f g δ)

/-- 実完全三角形の完備導来底変換は実完全三角形。 -/
theorem completedBaseChangeTriangle_distinguished
    (hT : Triangle.mk f.hom g.hom
      (δ.hom ≫ (DerivedCategory.Minus.ι.commShiftIso (1 : ℤ)).hom.app X) ∈
        distTriang (ConcreteDerivedCategory R)) :
    completedBaseChangeTriangle φ a f g δ ∈ distTriang (ConcreteDerivedCategory B) :=
  (derivedComplexCompletionFunctor B (φ a)).map_distinguished _
    (boundedAboveLeftDerivedTriangle_distinguished (ModuleCat.extendScalars φ) f g δ hT)

end SerrePositivity.DerivedCompletion
