module

public import SerrePositivity.InfinityCategories.F2.Idempotent.FibrationComplete

/-!
概要：冪等完備な元の ∞ 圏の slice と coslice は冪等完備。
方針：元の slice 射影の左右 fibration 性で、同じ全図式の強い分裂を持ち上げる。
規約：任意の形状の元の図式を扱い、添字の quasicategory 性は不要。
使われ方：HTT 5.1.4.3、冪等完備化の普遍性の準備。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 冪等完備な元の ∞ 圏の、任意の全図式上の slice は冪等完備。 -/
lemma sliceOver_isIdempotentComplete {K X : SSet.{u}} [Quasicategory X]
    (p : K ⟶ X) (hX : IsIdempotentComplete X) : IsIdempotentComplete (sliceOver p) :=
  isIdempotentComplete_of_rightFibration (sliceOverProjection p) hX

/-- 冪等完備な元の ∞ 圏の、任意の全図式下の coslice は冪等完備。 -/
lemma sliceUnder_isIdempotentComplete {K X : SSet.{u}} [Quasicategory X]
    (p : K ⟶ X) (hX : IsIdempotentComplete X) : IsIdempotentComplete (sliceUnder p) :=
  isIdempotentComplete_of_leftFibration (sliceUnderProjection p) hX

end SerrePositivity.InfinityCategories.F2.Idempotent
